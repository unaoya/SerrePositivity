module
public import SerrePositivity.KST.SConstruction.SCofiberIso

/-! # 二重 S 構成の二方向の転置
概要：S_m(S_n C) の全 gapped 図式を、S_m C を値とする Ar[n] 図式の族へ転置する。
方針：内部 Hom の交換を使い、Ar[n] の完全な評価によって各転置成分の gapped 性を得る。
規約：零図式の選択を変更しない。使われ方：内側と外側の S₁ の厳密な比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 二重 S 構成の二重内部 Hom への元の転置。 -/
def sInterchangeRawTranspose (m n : ℕ) (C : SSet.{u}) :
    sConstruction m (sConstruction n C) ⟶ (ihom (arNerve n)).obj ((ihom (arNerve m)).obj C) :=
  (gappedSubcomplex m (sConstruction n C)).ι ≫
    (ihom (arNerve m)).map (gappedSubcomplex n C).ι ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso (arNerve m) (arNerve n) C).hom

/-- 二重 S 構成の転置は各頂点で元の族の内部 Hom の交換。 -/
lemma sInterchangeRawTranspose_vertex (m n : ℕ) (C : SSet.{u})
    (v : (sConstruction m (sConstruction n C)) _⦋0⦌) :
    (sInterchangeRawTranspose m n C).app (Opposite.op ⦋0⦌) v =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (arNerve m) (arNerve n) C
        (gappedDiagram v ≫ (gappedSubcomplex n C).ι)) := by
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (gappedDiagram v) = v.val :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve m) (sConstruction n C)).apply_symm_apply v.val
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso (arNerve m) (arNerve n) C).hom.app (Opposite.op ⦋0⦌)
    (((ihom (arNerve m)).map (gappedSubcomplex n C).ι).app (Opposite.op ⦋0⦌) v.val) = _
  rw [← hv]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_functorVertex (arNerve m) (arNerve n) C
    (gappedDiagram v ≫ (gappedSubcomplex n C).ι)

/-- 転置の全 Ar[n] 成分は元の全 gapped な Ar[m] 図式。 -/
lemma sInterchangeRawTranspose_gapped (m n : ℕ) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (s : ((arNerve n) ⊗ sConstruction m (sConstruction n C)) _⦋0⦌) :
    IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve m) C).symm
      ((uncurry (sInterchangeRawTranspose m n C)).app (Opposite.op ⦋0⦌) s)) := by
  rcases s with ⟨b, v⟩
  change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve m) C).symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b).app (Opposite.op ⦋0⦌)
      ((sInterchangeRawTranspose m n C).app (Opposite.op ⦋0⦌) v)))
  rw [sInterchangeRawTranspose_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex, flipFamily_vertex]
  exact (gappedDiagram_isGapped v).postcomp _
    ((gappedInclusion_preservesSConstructionData n C).comp
      (evaluateFunctorAt_preservesSConstructionData b))

/-- 転置の Ar[m] 条件を保った Ar[n] 値の族への持ち上げ。 -/
def sInterchangeTransposeDiagram (m n : ℕ) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    sConstruction m (sConstruction n C) ⟶ (ihom (arNerve n)).obj (sConstruction m C) :=
  curry (gappedFamilyLift (uncurry (sInterchangeRawTranspose m n C))
    (sInterchangeRawTranspose_gapped m n C))

/-- 転置の持ち上げは包含後に元の二重内部 Hom の転置を厳密に回収する。 -/
lemma sInterchangeTransposeDiagram_ι (m n : ℕ) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    sInterchangeTransposeDiagram m n C ≫ (ihom (arNerve n)).map (gappedSubcomplex m C).ι =
      sInterchangeRawTranspose m n C := by
  apply uncurry_injective
  rw [uncurry_natural_right, sInterchangeTransposeDiagram, uncurry_curry, gappedFamilyLift_ι]

end SerrePositivity.KST.SConstruction
