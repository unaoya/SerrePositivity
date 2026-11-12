module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSpanPosetShape
public import Mathlib.SetTheory.Cardinal.HasCardinalLT
/-!
概要：小さい離散添字の nerve を、同じ濃度の離散 poset の nerve と厳密に比較する。
方針：ラベルを保持する型の wrapper と恒等の二関手から全単体同型を作る。
規約：添字の有限性や非空性を要求しない。
使われ方：D-8 c5 の可算・κ 未満の余積への P-9 の適用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet

@[ext] structure DGKappaDiscretePoset (J : Type u) : Type u where
  val : J

instance (J : Type u) : PartialOrder (DGKappaDiscretePoset J) where
  le a b := a.val = b.val
  le_refl _ := rfl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ h _ := DGKappaDiscretePoset.ext h

def dgKappaDiscretePosetToDiscrete (J : Type u) : DGKappaDiscretePoset J ⥤ Discrete J where
  obj a := ⟨a.val⟩
  map f := eqToHom (congrArg Discrete.mk (leOfHom f))

def dgKappaDiscreteToPoset (J : Type u) : Discrete J ⥤ DGKappaDiscretePoset J where
  obj a := ⟨a.as⟩
  map f := homOfLE (Discrete.eq_of_hom f)

def dgKappaDiscretePosetNerveIso (J : Type u) :
    nerve (DGKappaDiscretePoset J) ≅ nerve (Discrete J) where
  hom := nerveMap (dgKappaDiscretePosetToDiscrete J)
  inv := nerveMap (dgKappaDiscreteToPoset J)
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    change (s ⋙ dgKappaDiscretePosetToDiscrete J) ⋙ dgKappaDiscreteToPoset J = s
    have h : ∀ i, ((s ⋙ dgKappaDiscretePosetToDiscrete J) ⋙
        dgKappaDiscreteToPoset J).obj i = s.obj i := by
      intro i
      apply DGKappaDiscretePoset.ext
      rfl
    exact ComposableArrows.ext h (fun _ _ => Subsingleton.elim _ _)
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    change (s ⋙ dgKappaDiscreteToPoset J) ⋙ dgKappaDiscretePosetToDiscrete J = s
    have h : ∀ i, ((s ⋙ dgKappaDiscreteToPoset J) ⋙
        dgKappaDiscretePosetToDiscrete J).obj i = s.obj i := by
      intro i
      change Discrete.mk (s.obj i).as = s.obj i
      cases s.obj i
      rfl
    exact ComposableArrows.ext h (fun _ _ => Subsingleton.elim _ _)

lemma dgKappaDiscretePoset_hasCardinalLT (J : Type u) {κ : Cardinal.{u}}
    (hJ : HasCardinalLT J κ) : HasCardinalLT (DGKappaDiscretePoset J) κ :=
  hJ.of_injective DGKappaDiscretePoset.val (fun _ _ h => DGKappaDiscretePoset.ext h)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
