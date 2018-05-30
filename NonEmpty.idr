%default total

||| A "container" is non-empty if,
||| It is isomorphic to List X, and calling toList on it returns a cons-cell

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

postulate cons_correct_1 : (x : Char) -> (xs : String) -> unpack (strCons x xs) = x :: unpack xs

cons_correct_2 : (x : Char) -> (xs : List Char) -> x :: xs = unpack (strCons x (pack xs))
cons_correct_2 x [] = rewrite cons_correct_1 x "" in Refl
cons_correct_2 x (a :: as) =
  rewrite cons_correct_2 a as in
  rewrite cons_correct_1 x (strCons a (pack as)) in
  Refl

uncons : String -> Maybe (Char, String)
uncons a =
  case unpack a of
    [] => Nothing
    x :: xs => Just (x, pack xs)

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
  unpack_pack_id (x :: xs) = rewrite sym (cons_correct_2 x xs) in Refl

%language ElabReflection

nonEmpty_emptyStr_impossible : NonEmpty "" -> Void
nonEmpty_emptyStr_impossible (MkNonEmpty "" _ iso isCons) =
  %runElab (do
    debug {a=()}
    )

decStringNonEmpty : (s : String) -> Dec (NonEmpty s)
decStringNonEmpty s with (strM s)
  decStringNonEmpty "" | StrNil = No nonEmpty_emptyStr_impossible
  decStringNonEmpty (strCons a rest) | StrCons a rest = ?h1
