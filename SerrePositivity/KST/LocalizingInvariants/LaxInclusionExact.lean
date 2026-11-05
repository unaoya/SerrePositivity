module

public import SerrePositivity.KST.LocalizingInvariants.LaxInclusions
public import SerrePositivity.KST.LocalizingInvariants.ZeroMaps

/-!
概要：元の lax pullback の両包含は完全関手である。
方針：零対象と cofiber 列を両射影で判定し、零関手と恒等関手へ還元する。
規約：完全性を包含の入力にしない。使われ方：K-8 の半直交分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxInclusion

variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

lemma preservesZero_of_components {K : SSet.{u}} (F : K ⟶ (laxCategory p q).obj)
    [IsExactFunctor (F ≫ (laxFst p q).hom)] [IsExactFunctor (F ≫ (laxSnd p q).hom)] :
    PreservesZeroVertices F := by
  intro x hx
  have hc := IsExactFunctor.preservesZero (F := F ≫ (laxFst p q).hom) x hx
  have hd := IsExactFunctor.preservesZero (F := F ≫ (laxSnd p q).hom) x hx
  exact F2.isZeroVertex_laxPullback_of_components p.hom q.hom (F.app _ x) hc hd
    (IsExactFunctor.preservesZero (F := p.hom) _ hc)
    (IsExactFunctor.preservesZero (F := q.hom) _ hd)

lemma exact_of_components {K : SSet.{u}} (F : K ⟶ (laxCategory p q).obj)
    [IsExactFunctor (F ≫ (laxFst p q).hom)] [IsExactFunctor (F ≫ (laxSnd p q).hom)] :
    IsExactFunctor F where
  preservesZero := preservesZero_of_components p q F
  preservesCofiber t ht := by
    apply (F2.isPushoutSquare_laxPullback_iff_of_zero_corner p.hom q.hom
      (t.map F (preservesZero_of_components p q F))).2
    exact ⟨IsExactFunctor.preservesCofiber (F := F ≫ (laxFst p q).hom) t ht,
      IsExactFunctor.preservesCofiber (F := F ≫ (laxSnd p q).hom) t ht⟩

instance fromD_isExact : IsExactFunctor (fromD p q) := by
  have hz : IsExactFunctor (zeroC : D.obj ⟶ C.obj) := isExact_of_zero_values _ (by
    intro x
    rw [_root_.SerrePositivity.InfinityCategories.Stable.Lax.LaxInclusion.zeroC, zeroDiagram_const_vertex]
    exact (chosenZeroVertex C.obj).isZero)
  have : IsExactFunctor (fromD p q ≫ (laxFst p q).hom) := (fromD_fst p q).symm ▸ hz
  have : IsExactFunctor (fromD p q ≫ (laxSnd p q).hom) :=
    (fromD_snd p q).symm ▸ inferInstanceAs (IsExactFunctor (𝟙 D.obj))
  exact exact_of_components p q _

instance fromC_isExact : IsExactFunctor (fromC p q) := by
  have hz : IsExactFunctor (zeroD : C.obj ⟶ D.obj) := isExact_of_zero_values _ (by
    intro x
    rw [_root_.SerrePositivity.InfinityCategories.Stable.Lax.LaxInclusion.zeroD, zeroDiagram_const_vertex]
    exact (chosenZeroVertex D.obj).isZero)
  have : IsExactFunctor (fromC p q ≫ (laxFst p q).hom) :=
    (fromC_fst p q).symm ▸ inferInstanceAs (IsExactFunctor (𝟙 C.obj))
  have : IsExactFunctor (fromC p q ≫ (laxSnd p q).hom) := (fromC_snd p q).symm ▸ hz
  exact exact_of_components p q _

/-- 元の D 包含を完全関手に束ねる。 -/
def exactFromD : ExactMap D (laxCategory p q) := ⟨fromD p q, inferInstance⟩

/-- 元の C 包含を完全関手に束ねる。 -/
def exactFromC : ExactMap C (laxCategory p q) := ⟨fromC p q, inferInstance⟩

end SerrePositivity.KST.LocalizingInvariants.LaxInclusion
