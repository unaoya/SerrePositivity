module

public import SerrePositivity.KST.Spectra.MappingOmegaSequence
public import SerrePositivity.KST.Spectra.ShiftedKanSequence
public import SerrePositivity.KST.Spectra.KanSequenceAdjointMap

/-!
概要：通常の loop 列への構造随伴が厳密な列の射になるための条件。
方針：構造可換式を curry し、内部 Hom 列の構造随伴の交換公式を使う。
規約：交換不変性を Ω 条件から仮定しない。使われ方：Sp の逆関手経路の評価。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.KanSequence

local instance ordinaryLoopCriterionKan (Z : PointedSimplicialSet.{u}) [SSet.KanComplex Z.right] :
    SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Z).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

local instance ordinaryMappingCriterionKan (A Z : PointedSimplicialSet.{u})
    [SSet.KanComplex Z.right] : SSet.KanComplex ((ihom A).obj Z).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 元の構造射の通常円に関する随伴。Kan 円への持ち上げを含まない。 -/
def ordinaryStructureAdjoint (X : KanSequence.{u}) (n : ℕ) :
    (X.level n).space ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (X.level (n + 1)).space :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv _ _ (X.sigma n)

/-- 随伴族の厳密な構造可換性は、二重随伴の円交換不変性に一致する。 -/
lemma ordinaryStructureAdjoint_comm_iff (X : KanSequence.{u}) (n : ℕ) :
    (PointedSimplicialSet.circle.{u} ◁ ordinaryStructureAdjoint X n ≫
        (mapping PointedSimplicialSet.circle.{u} X).sigma (n + 1) =
      X.sigma n ≫ ordinaryStructureAdjoint X (n + 1)) ↔
    ((ordinaryStructureAdjoint X n ≫
        (ihom PointedSimplicialSet.circle.{u}).map (ordinaryStructureAdjoint X (n + 1))) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso PointedSimplicialSet.circle.{u} PointedSimplicialSet.circle.{u}
          (X.level (n + 2)).space).hom =
      ordinaryStructureAdjoint X n ≫
        (ihom PointedSimplicialSet.circle.{u}).map (ordinaryStructureAdjoint X (n + 1))) := by
  rw [← (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (X.level n).space
    ((mapping PointedSimplicialSet.circle.{u} X).level (n + 2)).space).injective.eq_iff]
  change curry (_ ≫ _) = curry (_ ≫ _) ↔ _
  rw [curry_natural_left, curry_natural_right]
  change ordinaryStructureAdjoint X n ≫
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv ((mapping PointedSimplicialSet.circle.{u} X).level (n + 1)).space
      ((mapping PointedSimplicialSet.circle.{u} X).level (n + 1 + 1)).space
      ((mapping PointedSimplicialSet.circle.{u} X).sigma (n + 1)) =
    ordinaryStructureAdjoint X n ≫
      (ihom PointedSimplicialSet.circle.{u}).map (ordinaryStructureAdjoint X (n + 1)) ↔ _
  rw [mapping_adjoint]
  simp only [ordinaryStructureAdjoint, Category.assoc]

/-- 円交換不変性を証明できれば、構造随伴そのものを成分とする厳密な射を得る。 -/
def ordinaryStructureAdjointHom (X : KanSequence.{u})
    (h : ∀ n, (ordinaryStructureAdjoint X n ≫
        (ihom PointedSimplicialSet.circle.{u}).map (ordinaryStructureAdjoint X (n + 1))) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso PointedSimplicialSet.circle.{u} PointedSimplicialSet.circle.{u}
          (X.level (n + 2)).space).hom =
      ordinaryStructureAdjoint X n ≫
        (ihom PointedSimplicialSet.circle.{u}).map (ordinaryStructureAdjoint X (n + 1))) :
    Hom X (tail (mapping PointedSimplicialSet.circle.{u} X)) where
  app := ordinaryStructureAdjoint X
  comm n := (ordinaryStructureAdjoint_comm_iff X n).2 (h n)

/-- Ω 条件の下で二重の構造随伴も全基点 π 同型。交換不変性とは別の条件である。 -/
lemma ordinaryDoubleStructureAdjoint_piIsomorphism (X : KanSequence.{u})
    (hX : X.OmegaCondition) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (ordinaryStructureAdjoint X n ≫
      (ihom PointedSimplicialSet.circle.{u}).map (ordinaryStructureAdjoint X (n + 1))).right :=
  (hX n).comp (PointedMapping.post_piIsomorphism PointedSimplicialSet.circle.{u}
    (ordinaryStructureAdjoint X (n + 1)) (hX (n + 1)))

/-- 随伴族が通常の loop 列への厳密な射なら、二重 loop の円交換は π₀ 上で恒等になる。 -/
lemma ordinaryStructureAdjoint_comm_forces_swap_piZero (X : KanSequence.{u})
    (hX : X.OmegaCondition) (n : ℕ)
    (hc : PointedSimplicialSet.circle.{u} ◁ ordinaryStructureAdjoint X n ≫
        (mapping PointedSimplicialSet.circle.{u} X).sigma (n + 1) =
      X.sigma n ≫ ordinaryStructureAdjoint X (n + 1)) :
    SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso PointedSimplicialSet.circle.{u}
      PointedSimplicialSet.circle.{u} (X.level (n + 2)).space).hom.right = id := by
  let f := ordinaryStructureAdjoint X n ≫
    (ihom PointedSimplicialSet.circle.{u}).map (ordinaryStructureAdjoint X (n + 1))
  have hf := ordinaryDoubleStructureAdjoint_piIsomorphism X hX n
  have hs := (hf.piZero_bijective_at (PointedSimplicialSet.basepoint (X.level n).space)).2
  have he := congrArg Under.Hom.right ((ordinaryStructureAdjoint_comm_iff X n).1 hc)
  change f.right ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso PointedSimplicialSet.circle.{u}
      PointedSimplicialSet.circle.{u} (X.level (n + 2)).space).hom.right = f.right at he
  funext a
  obtain ⟨b, rfl⟩ := hs a
  change SSet.mapπ₀ _ (SSet.mapπ₀ f.right b) = SSet.mapπ₀ f.right b
  rw [← SSet.mapπ₀_comp_apply, he]

end SerrePositivity.KST.Spectra.KanSequence
