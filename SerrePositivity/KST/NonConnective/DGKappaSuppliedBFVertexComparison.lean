module
public import SerrePositivity.KST.NonConnective.DGKappaSuppliedBFConnectiveStructure
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFVertexComparison

/-!
概要：採用済み二頂点 Sp 比較の命題と、同じ実供給頂点への受け渡しを保持する。
方針：元の実核と実商だけの指定同型を、元の実四角形の頂点へ戻す。
規約：K-S• の同じ実スペクトル比較を使う。群同型だけから Sp 同型を推論しない。
使われ方：新 BF 構造辺を旧実核 K と実商 K の loop へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.NonConnective
local instance suppliedBFVertexCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：実核と実商の旧 K と実供給 BF 模型の実 Sp 頂点同型の供給命題。
方針：同じ有限入力の番号 0 と 3 だけを指定する。
規約：存在は主張せず、四辺の Sp 写像空間内比較は要求しない。
使われ方：同じ固定 K へ戻す二頂点の明示定理引数。 -/
def dgKappaSuppliedBFVertexComparison : Prop :=
  ∀ (c : Fin 4) (_ : c = 0 ∨ c = 3),
    let C := dgKappaNativeBFFiniteNativeObject R D I c
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum (sInputModel C.obj)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaNativeBFFiniteOmegaSpectrum R D I C)))

/-- 概要：同じ実供給四角形の始点は元の実核の新 BF 模型。
方針：元の実下辺の始点を回収する。
規約：旧 K 値と新 BF 模型を等号で同一視しない。
使われ方：二頂点供給の始点比較を元の全錐へ戻す。 -/
theorem dgKappaSuppliedBFSquare_source :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgKappaNativeCoherentBFSquare R D I) 0 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaNativeBFFiniteOmegaSpectrum R D I
        (dgKappaNativeBFFiniteNativeObject R D I 0)) := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareBottomEdge_source (dgKappaNativeCoherentBFSquare R D I)
  have hb := dgKappaNativeCoherentBFSquare_boundary R D I 0
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ dgKappaNativeCoherentBFSquare R D I = _ at hb
  rw [hb] at h
  have hv := congrArg (fun t : Sp.{max (u + 1) v} _⦋1⦌ =>
    Sp.{max (u + 1) v}.δ 1 t)
    (SSet.yonedaEquiv.apply_symm_apply
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeCoherentBFArrow R D I 0).hom).edge)
  exact h.symm.trans (hv.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge _).src_eq)

/-- 概要：同じ実供給四角形の終点は元の実商の新 BF 模型。
方針：元の実右辺の終点を回収する。
規約：旧 K 値と新 BF 模型を等号で同一視しない。
使われ方：二頂点供給の終点比較を元の loop へ戻す。 -/
theorem dgKappaSuppliedBFSquare_target :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgKappaNativeCoherentBFSquare R D I) 1 1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaNativeBFFiniteOmegaSpectrum R D I
        (dgKappaNativeBFFiniteNativeObject R D I 3)) := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target (dgKappaNativeCoherentBFSquare R D I)
  have hb := dgKappaNativeCoherentBFSquare_boundary R D I 1
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ dgKappaNativeCoherentBFSquare R D I = _ at hb
  rw [hb] at h
  have hv := congrArg (fun t : Sp.{max (u + 1) v} _⦋1⦌ =>
    Sp.{max (u + 1) v}.δ 0 t)
    (SSet.yonedaEquiv.apply_symm_apply
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaNativeCoherentBFArrow R D I 1).hom).edge)
  exact h.symm.trans (hv.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge _).tgt_eq)

/-- 概要：同じ実供給全錐の始点は同じ実核の新 BF 頂点。
方針：元の全錐の頂点評価と実下辺の始点を照合する。
規約：同じ実全錐を保持する。
使われ方：実構造辺に前合成する二頂点比較の行先。 -/
theorem dgKappaSuppliedBFFiberComparison_source :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (dgKappaNativeCoherentBFSquare R D I)).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaNativeBFFiniteOmegaSpectrum R D I
        (dgKappaNativeBFFiniteNativeObject R D I 0)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex_eq]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] (horn 2 2) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ dgKappaNativeCoherentBFSquare R D I)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cospanConeSquareIso_initialPoint,
    SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact dgKappaSuppliedBFSquare_source R D I

/-- 概要：採用済みの二頂点比較を K-S• の実供給で放電する。
方針：同じ I と同じ実核・実商の公開同型をそのまま代入する。
規約：整数群の抽象同型からの推論を使わない。
使われ方：固定 K の構造辺と反復列から二頂点比較の仮定を外す。 -/
theorem dgKappaSuppliedBFVertexComparison_of_sConstruction :
    dgKappaSuppliedBFVertexComparison R D I :=
  dgKappaNativeBFKernelQuotientVertexIso R D I

/-- 概要：元の実核 K を同じ実供給全錐の始点へ戻す指定同型。
方針：番号 0 の元の SOA 比較同型を同じ錐頂点へ読み替える。
規約：公開済みの実 Sp 同型を使い、整数群から構成しない。
使われ方：固定 K から元の新 BF 構造辺へ入る実始点比較。 -/
def dgKappaSuppliedBFSourceIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum (stableCategoryModel (dgKappaNativeKernelCategory R D I))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (dgKappaNativeCoherentBFSquare R D I)).vertex := by
  rw [dgKappaSuppliedBFFiberComparison_source]
  exact dgKappaNativeBFSOAVertexIso R D I (dgKappaNativeBFFiniteNativeObject R D I 0)

/-- 概要：元の実商 K を同じ実供給四角形の終点へ戻す指定同型。
方針：番号 3 の元の SOA 比較同型を同じ実四角形の終点へ読み替える。
規約：公開済みの実 Sp 同型を使い、実商は同じ未完備の値を保つ。
使われ方：新 BF 商の loop から元の Yoneda 完備化比較へ戻す。 -/
def dgKappaSuppliedBFTargetIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (kOmegaSpectrum
      (stableCategoryModel (dgKappaNativeSuspensionCategory R D I))))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (dgKappaNativeCoherentBFSquare R D I) 1 1) := by
  rw [dgKappaSuppliedBFSquare_target]
  exact dgKappaNativeBFSOAVertexIso R D I (dgKappaNativeBFFiniteNativeObject R D I 3)

end SerrePositivity.KST.NonConnective
