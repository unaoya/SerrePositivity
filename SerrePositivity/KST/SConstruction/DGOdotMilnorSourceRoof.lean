module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorFlatKernelNullSquare
public import SerrePositivity.KST.SConstruction.DGKUniverseMorita
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorCoherence
public import SerrePositivity.DifferentialGraded.Resolution.Cell

/-!
概要：元対角始域の cell 分解から同じ thick 平坦核への厳密比較を構成する。
方針：元の対角に沿う cell 比較を同じ resolved 商の零対象核へ因子化する。
規約：元始域は増大屋根の終端に保持し、S 内の逆増大を仮定しない。
使われ方：17:53 採用の d④ の元始域回収と、固定 ν の指定比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGOdotGluing R d) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isDGPretriangulated R d
local notation "A" => DGSmallPerfectBase R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.source d))
local notation "B" => DGOdotGluing R d
local notation "δ" => DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d)
local notation "P" => dgQuotientImage R (δ)
local notation "K" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernel R (B) (P)
local notation "T" => DGCategoryCellResolution.Source R (A)

/-- 概要：元対角の同じ cell 比較関手。
方針：既存の関手に沿う標準分解比較を使用する。規約：分解を選び直さない。
使われ方：thick 平坦核への厳密因子化の基礎。 -/
def dgOdotMilnorSourceCellComparison :
    DGFunctor R (T) (DGCategoryCellResolution.Source R (B)) :=
  DGCategoryCellResolution.comparisonFunctor R (A) (B) (δ)

/-- 概要：同じ cell 比較の全対象は同じ resolved 商の thick 核に入る。
方針：元対角の零化と増大上の零性反映を使用する。
規約：安定閉包だけで thick 核を代用しない。使われ方：実核への対象作用。 -/
lemma dgOdotMilnorSourceCellComparison_mem (x : T) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgThickClosureProperty R (DGCategoryCellResolution.Source R (B))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (B) (P)) ((dgOdotMilnorSourceCellComparison R d).obj x) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection_vertex_isZero_iff_thick R (B) (P) _).mp
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_flat_vertex_zero_iff R (B) (P) _).mp
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedQuotientFunctor R d).app _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((δ).obj x.val)))
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorResolvedQuotient_kills_diagonal R d x.val

/-- 概要：元始域の cell 分解から同じ thick 平坦核への実厳密 dg 関手。
方針：同じ cell 比較の全 Hom を保持して対象を核へ因子化する。
規約：元始域の置換は増大屋根で記録する。使われ方：d④ の左端比較辺。 -/
def dgOdotMilnorSourceKernelDGMap : DGFunctor R (T) (K) where
  obj x := ⟨(dgOdotMilnorSourceCellComparison R d).obj x,
    dgOdotMilnorSourceCellComparison_mem R d x⟩
  map x y := (dgOdotMilnorSourceCellComparison R d).map x y
  map_id x := (dgOdotMilnorSourceCellComparison R d).map_id x
  map_comp x y z := (dgOdotMilnorSourceCellComparison R d).map_comp x y z

/-- 概要：核への比較を含めると同じ cell 比較を厳密に回収する。
方針：元の同じ Hom 写像と包含の恒等写像を照合する。規約：全 dg 関手の等号。
使われ方：元対角と増大を含む可換図式。 -/
lemma dgOdotMilnorSourceKernelDGMap_inclusion :
    (dgOdotMilnorSourceKernelDGMap R d).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernelInclusion R (B) (P)) =
        dgOdotMilnorSourceCellComparison R d := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  simp only [DGFunctor.comp, EnrichedFunctor.comp_map, dgOdotMilnorSourceKernelDGMap,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernelInclusion, dgFullSubcategoryInclusion,
    Category.comp_id]
  change (dgOdotMilnorSourceCellComparison R d).map x y ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- 概要：核比較と元始域増大は元の同じ対角を介して厳密可換。
方針：同じ核包含の回収と cell 比較の増大可換式を使用する。
規約：元対角の対象・全 Hom 作用を保持する。使われ方：元始域の増大屋根。 -/
lemma dgOdotMilnorSourceKernelDGMap_augmentation :
    (dgOdotMilnorSourceKernelDGMap R d).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickKernelInclusion R (B) (P)) =
        (DGCategoryCellResolution.augmentation R (A)).comp (δ) := by
  change (dgOdotMilnorSourceKernelDGMap R d).comp
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernelInclusion R (B) (P)).comp
      (DGCategoryCellResolution.augmentation R (B))) = _
  rw [← strictDGFunctor_comp_assoc, dgOdotMilnorSourceKernelDGMap_inclusion]
  exact DGCategoryCellResolution.comparisonFunctor_augmentation R (A) (B) (δ)

/-- 概要：Milnor 条件から同じ厳密核比較の全 Hom 準同型性。
方針：D2 の元対角の全 Hom 判定を既存 cell 比較へ渡す。
規約：生成仮定を追加入力にしない。使われ方：ν 像の指定同値の構成。 -/
lemma dgOdotMilnorSourceKernelDGMap_homQuasiIso (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    HomQuasiIso (dgOdotMilnorSourceKernelDGMap R d) :=
  DGCategoryCellResolution.comparisonFunctor_homQuasiIso R (A) (B) (δ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorSmallPerfectDiagonal_homQuasiIso_of_milnor R d h)

/-- 概要：元対角始域の同じ cell 分解を固定 S に置く。
方針：元の全 Hom を保つ対象宇宙持ち上げ。規約：元入力への増大を後で保持する。
使われ方：元始域屋根の共通始域。 -/
def dgOdotMilnorSourceCellInput : PerfDGInput.{u, u + 1} R :=
  dgKUniverseInput.{u, u + 1, u + 1} R (T)

/-- 概要：元対角始域への実増大を同じ S の屋根の脚にする。
方針：同じ厳密 dg 増大を持ち上げる。規約：S 内の逆を作らない。
使われ方：元始域を屋根の終端として回収する。 -/
def dgOdotMilnorSourceAugmentationInputMap :
    dgOdotMilnorSourceCellInput R d ⟶ dgOdotDiagonalSourceInput R d :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1}
    (DGCategoryCellResolution.augmentation R (A)))

/-- 概要：同じ thick 平坦核への実厳密比較を固定 S の辺にする。
方針：構成した同じ dg 関手を持ち上げる。規約：元商と核を選び直さない。
使われ方：元始域増大屋根のもう一つの脚。 -/
def dgOdotMilnorSourceKernelInputMap :
    dgOdotMilnorSourceCellInput R d ⟶ dgOdotMilnorFlatKernelInput R d :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor.{u, u + 1, u + 1, u + 1, u + 1}
    (dgOdotMilnorSourceKernelDGMap R d))

/-- 概要：元始域増大の同じ完全な ν 像。
方針：固定界面の実射を型付きで回収する。規約：安定値を選び直さない。
使われ方：元入力への屋根の脚。 -/
abbrev dgOdotMilnorSourceAugmentationExactMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
    (dgKInputStableValue R (dgOdotMilnorSourceCellInput R d))
    (dgKInputStableValue R (dgOdotDiagonalSourceInput R d)) :=
  dgKInputNuMap R (dgOdotMilnorSourceAugmentationInputMap R d)

/-- 概要：同じ平坦核比較の完全な ν 像。
方針：固定界面の実射を型付きで回収する。規約：核と比較を保持する。
使われ方：始域回収屋根の核側の脚。 -/
abbrev dgOdotMilnorSourceKernelExactMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
    (dgKInputStableValue R (dgOdotMilnorSourceCellInput R d))
    (dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)) :=
  dgKInputNuMap R (dgOdotMilnorSourceKernelInputMap R d)

end SerrePositivity.KST.SConstruction
