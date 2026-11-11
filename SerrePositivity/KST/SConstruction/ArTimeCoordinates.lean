module
public import SerrePositivity.KST.SConstruction.Gapped
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.MappingSpaceMap

/-! # object S のホモトピーの時刻座標
概要：区間の単体の時刻を Ar[n] の区間の左端で読む。
方針：Ar[n] から左端への順序射の nerve を標準単体へ移す。
規約：右端に置き換えず左端に統一する。使われ方：自然同値による object S のホモトピー。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：Ar[n] の区間を左端へ送る順序写像。
方針：成分ごとの順序の第一射影。
規約：ULift で宇宙を合わせる。使われ方：時刻座標の形状。 -/
def arFirstEndpointOrder (n : ℕ) : Ar.{u} n →o ULift.{u} (Fin (n + 1)) where
  toFun a := ULift.up a.down.val.1
  monotone' _ _ h := h.1

/-- 概要：Ar[n] の nerve から左端を読む標準単体への射。
方針：左端射の nerve と標準単体の nerve 同型。
規約：n=0 も含む。使われ方：区間の単体から時刻を引き戻す。 -/
def arFirstEndpoint (n : ℕ) : arNerve.{u} n ⟶ Δ[n] :=
  nerveMap (arFirstEndpointOrder n).toFunctor ≫ (stdSimplex.isoNerve n).inv

/-- 概要：標準区間の n 単体を Ar[n] の左端で読む時刻の図式。
方針：単体の Yoneda 表示を左端射に後合成する。
規約：全ての時刻の頂点を保持する。使われ方：object S の単体ホモトピーの候補。 -/
def arTimeCoordinate {n : ℕ} (s : (Δ[1] : SSet.{u}) _⦋n⦌) : arNerve.{u} n ⟶ Δ[1] :=
  arFirstEndpoint n ≫ SSet.yonedaEquiv.symm s

/-- 概要：時刻座標は全ての面・退化の添字制限と厳密に両立する。
方針：各鎖の各頂点で左端と順序写像の合成を計算する。
規約：任意の Δ の射。使われ方：object S のホモトピーの自然性。 -/
lemma arTimeCoordinate_naturality {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (s : (Δ[1] : SSet.{u}).obj n) :
    arNerveMap α.unop.toOrderHom ≫ arTimeCoordinate s = arTimeCoordinate ((Δ[1]).map α s) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro x
  apply ULift.ext
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext r
  rfl

/-- 概要：定値の時刻の単体は Ar[n] 上でも同じ定値時刻。
方針：各鎖の全頂点で一定性を計算する。
規約：両端の時刻に共通。使われ方：object S のホモトピーの両端。 -/
lemma arTimeCoordinate_constant (n : ℕ) (i : Fin 2) :
    arTimeCoordinate (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm i) n) =
      (SSet.const (stdSimplex.obj₀Equiv.symm i) : arNerve.{u} n ⟶ Δ[1]) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro x
  apply ULift.ext
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext r
  rfl

end SerrePositivity.KST.SConstruction
