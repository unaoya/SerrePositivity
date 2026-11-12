module

public import SerrePositivity.KST.Spectra.CosimplicialSequenceReedyAdjoint
public import SerrePositivity.KST.Spectra.PostMappingIsomorphism

/-!
概要：任意の余単体 Kan Ω 列を、各段 Reedy Kan な余単体 Kan Ω 列へ置換する。
方針：Reedy 延長で作った随伴射を uncurry し、単位との厳密可換性で Ω 条件を移す。
規約：列の構造射の単射性は後続の BF 置換に任せる。単位は実際の余単体射。
使われ方：Goerss–Jardine VII §4、BF 1978 §2。任意の Ω 図式の通常 Tot。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.CosimplicialSequenceReedyReplacement
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 各余単体次数の置換された実際の Kan 列。 -/
def sequence (D : CosimplicialObject KanSequence.{u}) (j : SimplexCategory) :
    KanSequence.{u} where
  level n := {
    space := (level D n).obj j
    kan := PointedCosimplicialKanReplacement.kanComplex _ _ }
  sigma n := uncurry ((adjoint D n).app j)

/-- 構成した列の随伴構造は選択した Reedy 延長そのもの。 -/
lemma sequence_adjoint (D : CosimplicialObject KanSequence.{u})
    (j : SimplexCategory) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv ((sequence D j).level n).space
      ((sequence D j).level (n + 1)).space ((sequence D j).sigma n) =
        (adjoint D n).app j := curry_uncurry _

/-- Reedy 延長の自然性から得られる列の厳密な射。 -/
def sequenceMap (D : CosimplicialObject KanSequence.{u})
    {i j : SimplexCategory} (f : i ⟶ j) : sequence D i ⟶ sequence D j :=
  KanSequence.Hom.ofAdjoint (fun n ↦ (level D n).map f) (fun n ↦ by
    rw [sequence_adjoint, sequence_adjoint]
    exact (adjoint D n).naturality f)

/-- 置換した列の厳密な余単体図式。 -/
def diagram (D : CosimplicialObject KanSequence.{u}) :
    CosimplicialObject KanSequence.{u} where
  obj := sequence D
  map := sequenceMap D
  map_id j := by
    apply KanSequence.Hom.ext_app
    intro n
    exact (level D n).map_id j
  map_comp f g := by
    apply KanSequence.Hom.ext_app
    intro n
    exact (level D n).map_comp f g

/-- 元の Kan 列から置換列への構造と厳密に可換する射。 -/
def unitComponent (D : CosimplicialObject KanSequence.{u}) (j : SimplexCategory) :
    D.obj j ⟶ sequence D j :=
  KanSequence.Hom.ofAdjoint (fun n ↦ (levelUnit D n).app j) (fun n ↦ by
    rw [sequence_adjoint]
    exact NatTrans.congr_app (levelUnit_adjoint D n) j)

/-- 図式としての厳密な置換単位。 -/
def unitApp (D : CosimplicialObject KanSequence.{u}) : D ⟶ diagram D where
  app := unitComponent D
  naturality i j f := by
    apply KanSequence.Hom.ext_app
    intro n
    exact (levelUnit D n).naturality f

/-- 単位の各段は全基点の π_* 同型。 -/
lemma unit_piIsomorphism (D : CosimplicialObject KanSequence.{u})
    (j : SimplexCategory) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (((unitApp D).app j).app n).right :=
  PointedCosimplicialKanReplacement.unit_piIsomorphism (originalLevel D n) j

/-- 元の図式の Ω 条件は置換した実際の列にも成り立つ。 -/
lemma sequence_omegaCondition (D : CosimplicialObject KanSequence.{u})
    (hD : ∀ j, (D.obj j).OmegaCondition) (j : SimplexCategory) :
    (sequence D j).OmegaCondition := by
  intro n
  rw [sequence_adjoint]
  have h := (hD j n).comp
    (PointedMapping.post_piIsomorphism PointedSimplicialSet.circle.{u}
      ((levelUnit D (n + 1)).app j) (unit_piIsomorphism D j (n + 1)))
  have he := congrArg Under.Hom.right (NatTrans.congr_app (levelUnit_adjoint D n) j)
  change ((levelUnit D n).app j).right ≫ ((adjoint D n).app j).right =
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv ((D.obj j).level n).space
      ((D.obj j).level (n + 1)).space ((D.obj j).sigma n)).right ≫
      (PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
        ((levelUnit D (n + 1)).app j)).right at he
  rw [← he] at h
  exact (_root_.SerrePositivity.KST.Spectra.KanPiIsomorphism.cancel_left_atVertex (unit_piIsomorphism D j n)) h
    ((D.obj j).level n).space.basepoint

end
end SerrePositivity.KST.Spectra.CosimplicialSequenceReedyReplacement
