module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.PointedInterval
public import SerrePositivity.KST.Spectra.PointedMappingParameters
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction

/-!
概要：基点を固定する単体的区間の収縮。
方針：Core の標準単体の最初の頂点への収縮を使い、時刻の因子を右へ置く。
規約：時刻零は定数射、時刻一は恒等射。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。path space の収縮。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：単体的区間の始点への収縮を右時刻の写像として表す。
方針：Core の先頭頂点への prism 収縮の因子を交換する。
規約：区間と時刻はいずれも Δ[1]。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。path space の収縮。 -/
def intervalContractionMap : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ⊗ (Δ[1] : SSet.{u}) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right :=
  (β_ (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstContraction 1

/-- 概要：区間の収縮は基点である始点を全時刻で固定する。
方針：頂点列の最小値の計算を行う。
規約：パラメータ側に基点は要求しない。
使われ方：Goerss–Jardine I §7。点つき写像空間への curry。 -/
theorem intervalContraction_basepoint :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.hom ▷ (Δ[1] : SSet.{u}) ≫ intervalContractionMap =
      toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.hom := by
  ext m s
  apply stdSimplex.ext
  intro j
  change (if _ then (0 : Fin 2) else 0) = 0
  split_ifs <;> rfl

/-- 概要：区間の収縮を点つき写像空間の辺として表す。
方針：全時刻で基点を固定する写像をパラメータ付き curry する。
規約：時刻の単体集合は Δ[1]。
使われ方：Goerss–Jardine I §7、HTT A.3.3。path space の収縮。 -/
def intervalContraction : (Δ[1] : SSet.{u}) ⟶
    (PointedObject.basedHom _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}).right :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry _ _ intervalContractionMap intervalContraction_basepoint

/-- 概要：区間の収縮の時刻零は始点への定数射。
方針：頂点列の時刻零の分岐を計算する。
規約：右因子の時刻を固定する。
使われ方：Goerss–Jardine I §7。path space の収縮の初端。 -/
@[reassoc]
theorem intervalContraction_zero :
    (SSet.ι₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ⟶ _) ≫ intervalContractionMap =
      toUnit _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.hom := by
  ext m s
  apply stdSimplex.ext
  intro j
  rfl

/-- 概要：区間の収縮の時刻一は恒等射。
方針：頂点列の時刻一の分岐を計算する。
規約：右因子の時刻を固定する。
使われ方：Goerss–Jardine I §7。path space の収縮の終端。 -/
@[reassoc]
theorem intervalContraction_one :
    (SSet.ι₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u}.right ⟶ _) ≫ intervalContractionMap = 𝟙 _ := by
  ext m s
  apply stdSimplex.ext
  intro j
  rfl

end

end SerrePositivity.KST.Spectra
