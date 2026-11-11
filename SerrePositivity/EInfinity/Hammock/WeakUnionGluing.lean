module

public import SerrePositivity.EInfinity.Hammock.WeakPushoutGluing
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# 元の部分複体の像の和の弱同値の貼り合わせ

概要：二つの部分複体と交わりの比較が弱同値なら、元の和の比較も弱同値。
方針：元の部分複体の bicartesian square と検証済みの pushout の弱同値の貼り合わせを使う。
規約：元の全体の射を制限した同じ比較を扱い、全体の弱同値性は仮定しない。
使われ方：proper 図式の境界の有限な像の和。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

variable {X Y : SSet.{u}} (f : X ⟶ Y)

/-- 元の全体の射を、元の二つの部分複体へ制限した射。 -/
def mapSubcomplex {A : X.Subcomplex} {B : Y.Subcomplex}
    (h : ∀ k, Set.MapsTo (f.app k) (A.obj k) (B.obj k)) : A.toFunctor ⟶ B.toFunctor where
  app k := ↾fun x => ⟨f.app k x.val, h k x.property⟩
  naturality k l α := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact NatTrans.naturality_apply f α x.val

lemma mapSubcomplex_ι {A : X.Subcomplex} {B : Y.Subcomplex}
    (h : ∀ k, Set.MapsTo (f.app k) (A.obj k) (B.obj k)) :
    mapSubcomplex f h ≫ B.ι = A.ι ≫ f := rfl

lemma mapSubcomplex_inclusion {A B : X.Subcomplex} {A' B' : Y.Subcomplex}
    (hAB : A ≤ B) (hAB' : A' ≤ B')
    (hA : ∀ k, Set.MapsTo (f.app k) (A.obj k) (A'.obj k))
    (hB : ∀ k, Set.MapsTo (f.app k) (B.obj k) (B'.obj k)) :
    Subcomplex.homOfLE hAB ≫ mapSubcomplex f hB =
      mapSubcomplex f hA ≫ Subcomplex.homOfLE hAB' := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  rfl

lemma mapsToSubcomplexInf {A B : X.Subcomplex} {A' B' : Y.Subcomplex}
    (hA : ∀ k, Set.MapsTo (f.app k) (A.obj k) (A'.obj k))
    (hB : ∀ k, Set.MapsTo (f.app k) (B.obj k) (B'.obj k)) :
    ∀ k, Set.MapsTo (f.app k) ((A ⊓ B).obj k) ((A' ⊓ B').obj k) :=
  fun k _ hx => ⟨hA k hx.1, hB k hx.2⟩

lemma mapsToSubcomplexSup {A B : X.Subcomplex} {A' B' : Y.Subcomplex}
    (hA : ∀ k, Set.MapsTo (f.app k) (A.obj k) (A'.obj k))
    (hB : ∀ k, Set.MapsTo (f.app k) (B.obj k) (B'.obj k)) :
    ∀ k, Set.MapsTo (f.app k) ((A ⊔ B).obj k) ((A' ⊔ B').obj k) :=
  fun k _ hx => hx.elim (fun h => Or.inl (hA k h)) (fun h => Or.inr (hB k h))

lemma weakUnion_gluing {A B : X.Subcomplex} {A' B' : Y.Subcomplex}
    (hA : ∀ k, Set.MapsTo (f.app k) (A.obj k) (A'.obj k))
    (hB : ∀ k, Set.MapsTo (f.app k) (B.obj k) (B'.obj k))
    (hInf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (mapSubcomplex f (mapsToSubcomplexInf f hA hB)))
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (mapSubcomplex f hA))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (mapSubcomplex f hB)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (mapSubcomplex f (mapsToSubcomplexSup f hA hB)) := by
  have hP := (show Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) from
    { sup_eq := rfl, inf_eq := rfl }).isPushout
  have hP' := (show Subcomplex.BicartSq (A' ⊓ B') A' B' (A' ⊔ B') from
    { sup_eq := rfl, inf_eq := rfl }).isPushout
  exact weakPushout_gluing hP hP' (mapSubcomplex f (mapsToSubcomplexInf f hA hB))
    (mapSubcomplex f hA) (mapSubcomplex f hB)
    (mapSubcomplex f (mapsToSubcomplexSup f hA hB))
    (mapSubcomplex_inclusion f _ _ _ _) (mapSubcomplex_inclusion f _ _ _ _)
    (mapSubcomplex_inclusion f _ _ _ _) (mapSubcomplex_inclusion f _ _ _ _) hInf ha hb

end SerrePositivity.EInfinity.Hammock
