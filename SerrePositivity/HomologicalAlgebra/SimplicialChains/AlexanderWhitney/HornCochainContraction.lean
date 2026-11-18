module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.HornSimplicialContraction
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.CochainMapHomotopy
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.SimplexCounitContraction

/-!
# 元の正規化ホーン包含の擬同型性

概要：任意の正次元標準ホーン包含の normalizedFunctor 像は擬同型。
方針：ホーンの二つの実円柱を正規化し、余単位の自然性と二対三を使う。
規約：元の AW cochains と元の包含射。モデル構造・Kan–Quillen を入力しない。
使われ方：Sp の β6 f4c の実ホーン充填と既存の cofibration 判定。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.SimplicialChains.AlexanderWhitney
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (n : ℕ) (i : Fin (n + 2))

/-- 概要：標準ホーンの正規化複体から零単体への実収縮。
方針：min から定値への鎖ホモトピーを反転し、恒等へのものと合成する。
規約：元の単体的射の像を両方向の射とする。
使われ方：ホーンの元の AW 余単位のホモトピー同値性。 -/
def hornCochainContraction :
    HomotopyEquiv (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A (horn (n + 1) i)) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A (Δ[0] : SSet.{0})) where
  hom := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainMap A (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornContractionProjection n i)
  inv := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainMap A (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornContractionSection n i)
  homotopyHomInvId := by
    have h := (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainMapHomotopy A (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornContractionToConst n i)).symm.trans
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainMapHomotopy A (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornContractionToId n i))
    simpa only [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainMap, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using h
  homotopyInvHomId := Homotopy.ofEq (by
    rw [← CategoryTheory.Functor.map_comp]
    have h : _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornContractionSection n i ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornContractionProjection n i =
        𝟙 (Δ[0] : SSet.{0}) := stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [h, CategoryTheory.Functor.map_id])

/-- 概要：標準ホーンの元の AW 余単位を順射とするホモトピー同値。
方針：零単体への収縮とその既存の余単位の収縮を合成し、自然性で照合する。
規約：元の余単位自身を順射に指定する。
使われ方：元のホーン包含に対する二対三。 -/
def hornCochainCounitHomotopyEquiv :
    HomotopyEquiv (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A (horn (n + 1) i)) (𝟙_ (Complex A)) :=
  ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornCochainContraction A n i).trans (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounitStdSimplexHomotopyEquiv A ⦋0⦌)).copy
    (Homotopy.ofEq (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit_natural A (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornContractionProjection n i)))

/-- 概要：ホーンの収縮の順射は元の余単位。
方針：copy の定義を読む。規約：定義上の一致。
使われ方：同じ余単位の擬同型性の回収。 -/
@[simp] lemma hornCochainCounitHomotopyEquiv_hom :
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornCochainCounitHomotopyEquiv A n i).hom = _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (horn (n + 1) i) := rfl

/-- 概要：標準ホーンの元の AW 余単位自身は擬同型。
方針：同じ射を順射とする実ホモトピー同値を使う。
規約：係数環やホーン位置の制限なし。使われ方：二対三の一方の射。 -/
lemma cochainCounit_horn_quasiIso : QuasiIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (horn (n + 1) i)) :=
  (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.hornCochainCounitHomotopyEquiv A n i).quasiIso_hom

/-- 概要：元の標準ホーン包含の正規化像自身は擬同型。
方針：ホーンと標準単体の余単位を比較し、自然性と二対三を適用する。
規約：全 n と全 i、任意可換環。ModelCategory SSet 等の仮定なし。
使われ方：Sp の β6 f4c の元のホーン包含の実弱同値判定。 -/
lemma normalizedHornInclusion_quasiIso :
    QuasiIso ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map (horn (n + 1) i).ι) := by
  have hs : QuasiIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (stdSimplex.obj ⦋n + 1⦌)) :=
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounitStdSimplexHomotopyEquiv A ⦋n + 1⦌).quasiIso_hom
  have hh : QuasiIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainMap A (horn (n + 1) i).ι ≫
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (stdSimplex.obj ⦋n + 1⦌)) := by
    rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit_natural]
    exact _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit_horn_quasiIso A n i
  exact quasiIso_of_comp_right _ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (stdSimplex.obj ⦋n + 1⦌))

end SerrePositivity.SimplicialChains.AlexanderWhitney
