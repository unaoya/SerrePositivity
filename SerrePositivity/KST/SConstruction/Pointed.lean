module
public import SerrePositivity.KST.SConstruction.FullSubcomplexUniversalVertices
public import SerrePositivity.KST.SConstruction.FunctorInitialVertices
public import SerrePositivity.KST.SConstruction.DegeneratePushouts

/-! # S_n の零図式
概要：零頂点への定値図式は gapped であり、S_n の零対象となる。
方針：恒等辺の押し出し性と関手圏の点ごとの零対象判定を使う。
規約：零対象は空間全体を保ち、特定の選択に置き換えない。
使われ方：BGT §7 の基点と S_0 の可縮性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：零頂点への定値 Ar[n] 図式は gapped。
方針：対角は零、四角形は恒等辺の押し出しとなる。
規約：C は quasicategory、安定性は不要。使われ方：S_n の基点。 -/
lemma isGapped_const (n : ℕ) {C : SSet.{u}} [Quasicategory C]
    (z : C _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) : IsGapped (SSet.const z : arNerve n ⟶ C) := by
  constructor
  · intro j
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z 0)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact hz
  · intro i j k l hij hjk hkl
    rw [SSet.comp_const]
    have h := isPushoutSquare_fst (SSet.const z : (Δ[1] : SSet.{u}) ⟶ C)
    rwa [SSet.comp_const] at h

/-- 概要：S_n の零図式を実際の頂点として指定する。
方針：定値図式の関手頂点を全部分複体に含める。
規約：任意の零頂点 z に対して定義する。使われ方：基点の選択と零対象の存在。 -/
def sConstructionZeroVertex (n : ℕ) {C : SSet.{u}} [Quasicategory C]
    (z : C _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) : (sConstruction n C) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const z : arNerve n ⟶ C), by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
    change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) C).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) C (SSet.const z)))
    rw [Equiv.symm_apply_apply]
    exact isGapped_const n z hz⟩

/-- 概要：零図式は S_n の零対象。
方針：関手圏で点ごとに零対象であることを示し、全部分複体へ移す。
規約：C は quasicategory。使われ方：全ての S_n の pointed 条件。 -/
lemma sConstructionZeroVertex_isZero (n : ℕ) {C : SSet.{u}} [Quasicategory C]
    (z : C _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (sConstructionZeroVertex n z hz) := by
  have ha : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const z : arNerve n ⟶ C)) := by
    apply isZeroVertex_functorVertex_of_pointwise
    intro a
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z 0)
    rwa [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
  exact ⟨isInitialVertex_fullSubcomplex_of_ambient _ _ ha.1,
    isTerminalVertex_fullSubcomplex_of_ambient _ _ ha.2⟩

/-- 概要：S• の全ての単体作用は同じ零対象の零図式を厳密に保つ。
方針：定値図式の前合成が定値図式に等しいことを使う。
規約：同型でなく実際の頂点の等号。使われ方：K 空間の単体的な基点。 -/
lemma sMap_zeroVertex {m n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (θ : Fin (m + 1) →o Fin (n + 1)) (z : C _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) :
    (sMap C θ).app (Opposite.op ⦋0⦌) (sConstructionZeroVertex n z hz) =
      sConstructionZeroVertex m z hz := by
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (arNerveMap θ ≫ (SSet.const z : arNerve n ⟶ C)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const z : arNerve m ⟶ C)
  rw [SSet.comp_const]

/-- 概要：零対象を持つ quasicategory の S_n も零対象を持つ。
方針：選んだ零対象の定値図式を使う。
規約：安定性は不要。使われ方：反復 S• の基点。 -/
instance sConstruction_hasZeroVertex (n : ℕ) (C : SSet.{u}) [Quasicategory C]
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C] : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex (sConstruction n C) where
  exists_zero := ⟨sConstructionZeroVertex n (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C).vertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C).isZero,
    sConstructionZeroVertex_isZero n _ _⟩

/-- 概要：S_0 の全ての頂点は零対象。
方針：Ar[0] の唯一の対象は対角であり、関手圏の点ごとの零対象判定が適用できる。
規約：C は quasicategory。使われ方：S_0 の可縮性。 -/
lemma sConstructionZero_isZeroVertex (C : SSet.{u}) [Quasicategory C]
    (v : (sConstruction 0 C) _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex v := by
  have ha : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex v.val := by
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (gappedDiagram v) = v.val :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply _
    rw [← he]
    apply isZeroVertex_functorVertex_of_pointwise
    intro a
    have h : a = ComposableArrows.mk₀ (arObj (0 : Fin 1) 0 le_rfl) := by
      refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
      apply ULift.ext
      apply Subtype.ext
      apply Prod.ext <;> exact Fin.eq_zero _
    rw [h]
    exact (gappedDiagram_isGapped v).1 0
  exact ⟨isInitialVertex_fullSubcomplex_of_ambient _ _ ha.1,
    isTerminalVertex_fullSubcomplex_of_ambient _ _ ha.2⟩

/-- 概要：零対象を持つ quasicategory の S_0 は可縮な Kan 複体。
方針：零次元は零図式の存在、正次元は各頂点の終対象性で境界を充填する。
規約：core を取る前の S_0 自体の主張。使われ方：単体的 K 空間の零段。 -/
lemma sConstructionZero_isContractibleKan (C : SSet.{u}) [Quasicategory C]
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (sConstruction 0 C) := by
  intro n b
  cases n with
  | zero =>
    exact ⟨SSet.const (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex (sConstruction 0 C)).vertex, boundary.hom_ext₀⟩
  | succ n =>
    let v := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b)
    exact (sConstructionZero_isZeroVertex C v).2 n b
      (SSet.yonedaEquiv.symm_apply_apply _).symm

/-- 概要：S_0 は Kan 複体。
方針：全境界の充填から従う。
規約：C は零対象を持つ quasicategory。使われ方：K 空間の基点の零段。 -/
instance sConstructionZero_kanComplex (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C] :
    KanComplex (sConstruction 0 C) := (sConstructionZero_isContractibleKan C).kanComplex

/-- 概要：空の第一行の関手単体集合への射は一意。
方針：内部 Hom の各成分で、空の添字の鎖の対象が存在しないことを使う。
規約：A と C は任意。使われ方：第一行制限の n=0 の持ち上げの右側の等号。 -/
lemma firstRowZero_hom_ext {A C : SSet.{u}}
    (f g : A ⟶ (ihom (firstRowNerve 0)).obj C) : f = g := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  apply CategoryTheory.Functor.functorHom_ext
  intro e α
  apply ConcreteCategory.hom_ext
  intro x
  exact isEmptyElim (x.obj 0).down

/-- 概要：零段の第一行制限は trivial Kan fibration。
方針：可縮な S_0 で全境界を充填し、空の第一行への射の一意性を使う。
規約：C は零対象を持つ quasicategory、安定性は不要。
使われ方：L1b の n=0 の完全な持ち上げ性。 -/
instance firstRowRestriction_zero_trivialKanFibration (C : SSet.{u}) [Quasicategory C]
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (firstRowRestriction 0 C) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  obtain ⟨F, hF⟩ := sConstructionZero_isContractibleKan C n a
  exact CommSq.HasLift.mk' {
    l := F
    fac_left := hF
    fac_right := firstRowZero_hom_ext _ _ }

end SerrePositivity.KST.SConstruction
