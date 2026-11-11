module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MooreCycles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MooreHomology
public import Mathlib.Algebra.Group.TypeTags.Hom

/-! # 導来写像空間の正次数ホモトピー群

概要：実際の右 pinched 写像空間の正次数 π は Hom 複体の負次数コホモロジーに同型である。
方針：K-L9 の充填による群を Moore cycles の境界商へ送り、Moore 複体の同型を合成する。
規約：π の次数は n+1、基点は零写像。使われ方：D10 の正次数の写像空間の計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded AlgebraicTopology
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial

/-- 概要：加法群の同型を乗法表記の群の同型にする。
方針：AddMonoidHom の標準変換と全単射性を使う。
規約：Multiplicative は台の型を変えない。使われ方：π とコホモロジーの比較。 -/
def additiveGroupToMultiplicativeEquiv {A : Type v} {B : Type w}
    [AddGroup A] [AddGroup B] (e : A ≃+ B) : Multiplicative A ≃* Multiplicative B :=
  MulEquiv.ofBijective e.toAddMonoidHom.toMultiplicative e.bijective

/-- 概要：単体集合の同型は基点の像で正次数 π の群同型を誘導する。
方針：両方向の誘導準同型に単体的同型の逆則を適用する。
規約：K-L9 の次数 n+1。使われ方：実際の pinched 空間とその線形化の比較。 -/
def kanHomotopyGroupIsoEquiv {X Y : SSet.{v}} [SSet.KanComplex X] [SSet.KanComplex Y]
    (e : X ≅ Y) (n : ℕ) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x ≃* _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y n (e.hom.app _ x) := by
  have hi : e.inv.app _ (e.hom.app _ x) = x := by
    change (e.hom ≫ e.inv).app _ x = x
    rw [Iso.hom_inv_id]
    rfl
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) (x := x) e.hom rfl
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) e.inv hi
  refine { toFun := F, invFun := G, left_inv := ?_, right_inv := ?_, map_mul' := F.map_mul }
  · intro a
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp (n := n) (x := x) (y := e.hom.app _ x) (z := x)
      e.hom rfl e.inv hi
      (show (e.hom ≫ e.inv).app _ x = x by rw [Iso.hom_inv_id]; rfl)
    have hh : G.comp F = MonoidHom.id _ := by
      rw [← h]
      simp only [Iso.hom_inv_id, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_id]
    exact DFunLike.congr_fun hh a
  · intro a
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp (n := n) (x := e.hom.app _ x) (y := x)
      (z := e.hom.app _ x) e.inv hi e.hom rfl
      (show (e.inv ≫ e.hom).app _ (e.hom.app _ x) = e.hom.app _ x by rw [Iso.inv_hom_id]; rfl)
    have hh : F.comp G = MonoidHom.id _ := by
      rw [← h]
      simp only [Iso.inv_hom_id, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_id]
    exact DFunLike.congr_fun hh a

variable {S : Type u} [CommRing S]

/-- 概要：単体的加群の正次数 π は Moore ホモロジーと群同型である。
方針：球面単体の境界商による二つの表示を合成する。
規約：Kan 性を明示する。使われ方：写像空間の線形計算の一般定理。 -/
def modulePiMooreGroupEquiv (W : SimplicialObject (ModuleCat.{v} S))
    [SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W)] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) n 0 ≃*
      Multiplicative (((normalizedMooreComplex (ModuleCat.{v} S)).obj W).homology (n + 1)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.modulePiSphereGroupEquiv W n).trans
    (additiveGroupToMultiplicativeEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mooreHomologySphereIso W n).symm.toLinearEquiv.toAddEquiv)

variable {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory S D]

open SSet.modelCategoryQuillen in
/-- 概要：実際の pinched 空間の線形化の台は Kan 複体である。
方針：N4 の Kan 性を忘却後の同型で移す。
規約：実際の右 pinched 単体の台。使われ方：K-L9 の π の入力。 -/
instance pinchedHomModuleUnderlyingKan (x y : D) :
    SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModule (S := S) x y)) :=
  HomotopicalAlgebra.isFibrant_of_fibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModuleForgetIso x y).hom

/-- 概要：右 pinched 写像空間の零写像の基点。
方針：実際の線形化の零頂点を忘却する。
規約：N4 の零閉射。使われ方：ホモトピー群の基点の固定。 -/
def pinchedHomZeroVertex (x y : D) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom S D x y) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModuleForgetIso x y).hom.app _ 0

/-- 概要：実際の右 pinched 写像空間の π_{n+1} は H^{-n-1} Hom と群同型である。
方針：線形化の π、Moore ホモロジー、Hom コホモロジー、ULift の除去を合成する。
規約：零写像を基点とする。使われ方：D10 の正次数の導来写像空間の計算。 -/
def pinchedHomPiCohomologyEquiv (x y : D) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom S D x y) n (pinchedHomZeroVertex x y) ≃*
      Multiplicative ((_root_.SerrePositivity.DifferentialGraded.homObject S D x y).homology (-((n + 1 : ℕ) : ℤ))) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.kanHomotopyGroupIsoEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModuleForgetIso x y) n 0).symm.trans
    ((modulePiMooreGroupEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomModule x y) n).trans
      ((additiveGroupToMultiplicativeEquiv
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomMooreHomologyIso x y (n + 1)).toLinearEquiv.toAddEquiv).trans
          (additiveGroupToMultiplicativeEquiv (ULift.moduleEquiv (R := S)).toAddEquiv)))

/-- 概要：D(S) の二頂点の正次数写像ホモトピー群は semifree Hom の負コホモロジーである。
方針：任意 dg 圏の群同型を Semifree(S) に適用する。
規約：任意の可換環、非有界複体を含む。使われ方：導来 Ext 計算への入力。 -/
def derivedInfinityPiCohomologyEquiv (x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) (x.obj 0) (y.obj 0)) n
      (pinchedHomZeroVertex (x.obj 0) (y.obj 0)) ≃*
        Multiplicative ((_root_.SerrePositivity.DifferentialGraded.homObject S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) (x.obj 0) (y.obj 0)).homology
          (-((n + 1 : ℕ) : ℤ))) :=
  pinchedHomPiCohomologyEquiv (x.obj 0) (y.obj 0) n

end SerrePositivity.InfinityCategories.Project.DerivedCategories
