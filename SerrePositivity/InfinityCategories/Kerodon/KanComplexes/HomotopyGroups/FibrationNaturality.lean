module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationBoundary

/-!
概要：Kan fibration の射に対する fiber と連結写像の自然性。
方針：引き戻しの普遍性で fiber の射を作り、相対ホーンの持ち上げを後合成する。
規約：可換四角形は厳密に可換とし、底と全空間の基点の像を明示する。
使われ方：Kerodon §§3.2.5（Tag 00WD）–3.2.6（Tag 00WL）、Goerss–Jardine I §§7–8。長完全列の自然性。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Spectra.FibrationSquare
end SerrePositivity.KST.Spectra.FibrationSquare
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

/-- 概要：fiber の二つの頂点は全空間への像が同じなら等しい。
方針：頂点を Yoneda で写像に変え、fiber の普遍性の一意性を使う。
規約：底の基点は b。
使われ方：Kerodon §3.2.5（Tag 00WD）。fiber 間の射の基点保存。 -/
theorem fiber_vertex_ext {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌)
    (v w : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p b) _⦋0⦌) (h : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b).app _ v = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p b).app _ w) : v = w := by
  apply yonedaEquiv.symm.injective
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p b
  apply yonedaEquiv.injective
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply] using h

namespace FibrationSquare
open _root_.SerrePositivity.KST.Spectra.FibrationSquare

variable {E B E' B' : SSet.{u}} (p : E ⟶ B) (p' : E' ⟶ B')
  (f : E ⟶ E') (g : B ⟶ B') (comm : p ≫ g = f ≫ p')

include comm in
/-- 概要：可換四角形は全空間の頂点の底への像を保つ。
方針：可換条件を零単体で評価する。
規約：標的の全空間の基点は f(e)。
使われ方：Kerodon §3.2.5（Tag 00WD）。底の誘導準同型の基点。 -/
theorem base_eq (e : E _⦋0⦌) : g.app _ (p.app _ e) = p'.app _ (f.app _ e) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app comm _) e

/-- 概要：可換四角形が誘導する頂点上の fiber 間の射。
方針：全空間への包含を f と合成し、標的 fiber の普遍性を使う。
規約：始域は p(e) 上、終域は p'(f(e)) 上。
使われ方：Kerodon §3.2.5（Tag 00WD）。fiber 列の自然性。 -/
noncomputable def fiberMap (e : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p' (p'.app _ (f.app _ e)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift p' (p'.app _ (f.app _ e)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e) ≫ f) (by
    rw [Category.assoc, ← comm, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_comp, const_comp,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p p' f g comm e])

/-- 概要：fiber 間の射を含めると全空間の可換四角形の射となる。
方針：fiber への持ち上げの第一成分を読む。
規約：基点は f(e) を用いる。
使われ方：Kerodon §3.2.5（Tag 00WD）。fiber 列の射の計算。 -/
@[reassoc (attr := simp)]
theorem fiberMap_ι (e : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap p p' f g comm e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p' (p'.app _ (f.app _ e)) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι p (p.app _ e) ≫ f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι _ _ _ _

/-- 概要：fiber 間の射は指定された基点を保つ。
方針：全空間への包含で比較し、零単体で fiberMap_ι を評価する。
規約：標的の基点は f(e) の持ち上げ。
使われ方：Kerodon §3.2.5（Tag 00WD）。fiber のホモトピー群の誘導写像。 -/
@[simp]
theorem fiberMap_point (e : E _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap p p' f g comm e).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p' (f.app _ e) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_vertex_ext p' (p'.app _ (f.app _ e))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point]
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap_ι p p' f g comm e) _) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e)
  simpa only [NatTrans.comp_app, types_comp_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point] using h

/-- 概要：相対ホーンの持ち上げを可換四角形の射で後合成できる。
方針：全空間の射 f と合成し、底の可換条件で相対持ち上げを確認する。
規約：底の代表単体も g で後合成する。
使われ方：Kerodon §3.2.5（Tag 00WD）。連結写像の自然性。 -/
def mappedLift (e : E _⦋0⦌) {n : ℕ} {s : B.PtSimplex (n + 1) (p.app _ e)}
    (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p' (f.app _ e) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex g (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p p' f g comm e) s) where
  map := L.map ≫ f
  map_comp := by
    rw [Category.assoc, ← comm, ← Category.assoc, L.map_comp]
    rfl
  face_eq j hj := by rw [← Category.assoc, L.face_eq j hj, const_comp]

/-- 概要：持ち上げの境界を後合成する操作は fiber 間の射と可換。
方針：標的 fiber の包含で比較し、最後の面と後合成の結合則を使う。
規約：零次数の境界も含む。
使われ方：Kerodon §3.2.5（Tag 00WD）。連結写像の自然性の代表上の計算。 -/
theorem mappedLift_boundary (e : E _⦋0⦌) {n : ℕ} {s : B.PtSimplex (n + 1) (p.app _ e)}
    (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.mappedLift p p' f g comm e L).boundary =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap p p' f g comm e) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap_point p p' f g comm e) L.boundary := by
  ext : 1
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext p' (p'.app _ (f.app _ e))
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.mappedLift, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex, Category.assoc]

/-- 概要：Kan fibration の可換四角形に対して連結写像は全次数で自然。
方針：元の相対持ち上げを後合成して標的の計算に使い、境界の自然性を適用する。
規約：標的の次数 n = 0 も基点付き集合として含む。
使われ方：Kerodon §§3.2.5（Tag 00WD）–3.2.6（Tag 00WL）。ホモトピー長完全列の自然性。 -/
theorem connecting_natural [Fibration p] [Fibration p'] [KanComplex B] [KanComplex B']
    (e : E _⦋0⦌) (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B n (p.app _ e)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap p p' f g comm e) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap_point p p' f g comm e)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e n a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p' (f.app _ e) n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p p' f g comm e) a) := by
  induction a using Quotient.inductionOn with | h s => ?_
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap p p' f g comm e) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap_point p p' f g comm e)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p' (f.app _ e) n
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p p' f g comm e) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s))
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.chooseBoundaryLift p e s
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting_eq p e L, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_mk, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting_eq p' (f.app _ e) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.mappedLift p p' f g comm e L), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.mappedLift_boundary]

end FibrationSquare

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.fiber_vertex_ext := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_vertex_ext

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.base_eq := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.connecting_natural := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.connecting_natural

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.fiberMap := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.fiberMap_point := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap_point

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.fiberMap_ι := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap_ι

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.fiberMap_ι_assoc := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap_ι_assoc

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.mappedLift (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.mappedLift := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.mappedLift

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.mappedLift_boundary := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.mappedLift_boundary

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.fiberMap._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.fiberMap.congr_simp := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.fiberMap.congr_simp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.mappedLift._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.mappedLift._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.mappedLift._proof_2 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.mappedLift._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationSquare.mappedLift.eq_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.mappedLift.eq_1
