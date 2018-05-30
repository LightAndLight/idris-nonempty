%default total

||| A "container" is non-empty if,
||| It is isomorphic to List X, and calling toList on it returns a cons-cell
|||
||| Wrong?

record Iso a b where
  constructor MkIso
  to : a -> b
  from : b -> a
  to_from_id : (x : a) -> from (to x) = x
  from_to_id : (x : b) -> to (from x) = x

reflIso : Iso a a
reflIso =
  MkIso
    id
    id
    (\_ => Refl)
    (\_ => Refl)

transIso : Iso b c -> Iso a b -> Iso a c
transIso iso_bc iso_ab =
  MkIso
    (to iso_bc . to iso_ab)
    (from iso_ab . from iso_bc)
    (\x =>
       rewrite to_from_id iso_bc (to iso_ab x) in
       rewrite to_from_id iso_ab x in
       Refl)
    (\x =>
       rewrite from_to_id iso_ab (from iso_bc x) in
       rewrite from_to_id iso_bc x in
       Refl)

symIso : Iso a b -> Iso b a
symIso iso_ab =
  MkIso
    (from iso_ab)
    (to iso_ab)
    (from_to_id iso_ab)
    (to_from_id iso_ab)

data Cons : List a -> Type where
  IsCons : {x : a} -> {xs : List a} -> Cons (x :: xs)

Uninhabited (Cons []) where
  uninhabited IsCons impossible

data NonEmpty : {a : Type} -> a -> Type where
  MkNonEmpty
     : (e : a)
    -> (element : Type)
    -> (list_iso : Iso a (List element))
    -> (is_nonempty : Cons (to list_iso e))
    -> NonEmpty e

||| I think this needs to be postulates because 'strCons' is a primitive
postulate unpackStrCons_consUnpack : (x : Char) -> (xs : String) -> unpack (strCons x xs) = x :: unpack xs

cons_unpackStrConsPack : (x : Char) -> (xs : List Char) -> x :: xs = unpack (strCons x (pack xs))
cons_unpackStrConsPack x [] = rewrite unpackStrCons_consUnpack x "" in Refl
cons_unpackStrConsPack x (a :: as) =
  rewrite cons_unpackStrConsPack a as in
  rewrite unpackStrCons_consUnpack x (strCons a (pack as)) in
  Refl

strListIso : Iso String (List Char)
strListIso =
  MkIso
    unpack
    pack
    pack_unpack_id
    unpack_pack_id
where
  pack_unpack_id : (x : String) -> pack (unpack x) = x
  pack_unpack_id x with (strM x)
    pack_unpack_id "" | StrNil = Refl
    pack_unpack_id (strCons a rest) | StrCons a rest =
      -- the assertion is necessary when working with StrM.
      -- see https://github.com/idris-lang/Idris-dev/blob/master/libs/prelude/Prelude/Strings.idr#L183
      assert_total (rewrite pack_unpack_id rest in Refl)

  unpack_pack_id : (x : List Char) -> unpack (pack x) = x
  unpack_pack_id [] = Refl
  unpack_pack_id (x :: xs) = rewrite sym (cons_unpackStrConsPack x xs) in Refl

decStringNonEmpty : (s : String) -> Dec (NonEmpty s)
decStringNonEmpty s with (strM s)
  decStringNonEmpty (strCons a rest) | StrCons a rest =
    Yes $ MkNonEmpty (strCons a rest) Char strListIso (rewrite unpackStrCons_consUnpack a rest in IsCons)
  decStringNonEmpty "" | StrNil = No nonEmpty_emptyStr_impossible
  where
    nonEmpty_emptyStr_impossible : NonEmpty "" -> Void
    nonEmpty_emptyStr_impossible (MkNonEmpty "" ty iso isCons) = absurd contradiction
      where
        implication : Cons (to iso "") -> (x : ty ** xs : List ty ** to iso "" = x :: xs)
        implication a with (to iso "")
          implication a | [] = absurd a
          implication a | (x :: xs) = (x ** xs ** Refl)

        -- we have a proof that 'to iso "" = x :: xs'
        --
        -- and because of congruence of equality
        -- 'from iso (to iso "") = from iso (x :: xs)'
        --
        -- but this states that
        --
        -- "" = from iso (x :: xs), which results in a non-empty string
        contradiction : Void
        contradiction =
          case implication isCons of
            (_ ** _ ** prf) => case cong {f=from iso} prf of Refl impossible

data Bin : Type -> Type where
  BinLeaf : Bin a
  BinBranch : Bin a -> a -> Bin a -> Bin a

data UnconsBin : Bin a -> (a, Bin a) -> Type where
  UnconsBinL : UnconsBin l (val, l') -> UnconsBin (BinBranch l a r) (val, BinBranch l' a r)
  UnconsBinR
     : Not (UnconsBin l (val, l'))
    -> UnconsBin r (val, r')
    -> UnconsBin (BinBranch l a r) (val, BinBranch l a r')
  UnconsBinTip
     : Not (UnconsBin l (val, l'))
    -> Not (UnconsBin r (val, r'))
    -> UnconsBin (BinBranch l a r) (a, BinLeaf)

Uninhabited (UnconsBin BinLeaf anything) where
  uninhabited UnconsBinL impossible
  uninhabited UnconsBinR impossible
  uninhabited UnconsBinTip impossible

unconsBin : Bin a -> Maybe (a, Bin a)
unconsBin b =
  case b of
    BinLeaf => Nothing
    BinBranch l a r =>
      case unconsBin l of
        Nothing => case unconsBin r of
          Nothing => Just (a, BinLeaf)
          Just (val, r') => Just (val, BinBranch BinLeaf a r')
        Just (val, l') => Just (val, BinBranch l' a r)

uncons_bin_consistent
   : (b : Bin a)
   -> case unconsBin b of
        Nothing => ()
        Just (val, b') => UnconsBin b (val, b')
uncons_bin_consistent BinLeaf = ()
uncons_bin_consistent (BinBranch l v r) with (unconsBin l)
  uncons_bin_consistent (BinBranch l v r) | Just (val, l') = ?hole1
  uncons_bin_consistent (BinBranch l v r) | Nothing with (unconsBin r)
    uncons_bin_consistent (BinBranch l v r) | Nothing | Just (val, r') = ?hole2
    uncons_bin_consistent (BinBranch l v r) | Nothing | Nothing = UnconsBinTip

binSize : Bin a -> Nat
binSize BinLeaf = Z
binSize (BinBranch l _ r) = binSize l + S (binSize r)

consBin : a -> Bin a -> Bin a
consBin v BinLeaf = BinBranch BinLeaf v BinLeaf
consBin v (BinBranch l v' r) =
  case compare (binSize l) (binSize r) of
    GT => BinBranch l v' (consBin v r)
    _ => BinBranch (consBin v l) v' r

uncons_cons_bin
  : (b : Bin a) ->
    case unconsBin b of
      Nothing => ()
      Just (v, b') => consBin v b' = b
uncons_cons_bin b with (unconsBin b)
  uncons_cons_bin b | Nothing = ()
  uncons_cons_bin b | Just (v, rest) = ?hole

binToList : Bin a -> List a
binToList b =
  case b of
    BinLeaf => []
    BinBranch l a r =>
      case unconsBin l of
        Nothing => a :: binToList r
        Just (val, l') =>
          -- I'd like to know how to make this work without the assert
          val :: binToList (assert_smaller (BinBranch l a r) (BinBranch l' a r))

listToBin : List a -> Bin a
listToBin = ?hh2

binListIso : {a : Type} -> Iso (Bin a) (List a)
binListIso {a} =
  MkIso
    binToList
    listToBin
    ?h1
    ?h2
