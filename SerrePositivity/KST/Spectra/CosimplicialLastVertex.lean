module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
概要：余単体圏の Bousfield–Kan 重みから標準単体の重みへの終頂点射。
方針：over 圏の対象である単体の終頂点を取り、可換三角形の単調性を使う。
規約：添字圏は AsSmall で係数と同じ宇宙に置く。
使われ方：Goerss–Jardine VII §4、VIII §1。通常 Tot から homotopy Tot への比較。
-/

@[expose] public section
universe u
open CategoryTheory SSet

open scoped Simplicial

namespace SerrePositivity.KST.Spectra.CosimplicialLastVertex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {j : AsSmall.{u} SimplexCategory}

/-- 終点 j を持つ単体の終頂点。 -/
def value (a : Over j) : Fin ((AsSmall.down.obj j).len + 1) :=
  (AsSmall.down.map a.hom).toOrderHom (Fin.last (AsSmall.down.obj a.left).len)

/-- over 圏の射は終頂点を単調に送る。 -/
lemma value_le {a b : Over j} (f : a ⟶ b) : value a ≤ value b := by
  have hh : AsSmall.down.map f.left ≫ AsSmall.down.map b.hom = AsSmall.down.map a.hom := by
    rw [← Functor.map_comp, Over.w]
  dsimp only [value]
  rw [← hh]
  change (AsSmall.down.map b.hom).toOrderHom
    ((AsSmall.down.map f.left).toOrderHom (Fin.last (AsSmall.down.obj a.left).len)) ≤ _
  exact (AsSmall.down.map b.hom).toOrderHom.monotone (Fin.le_last _)

/-- 終頂点を取る順序圏への関手。 -/
def functor (j : AsSmall.{u} SimplexCategory) :
    Over j ⥤ ULift.{u} (Fin ((AsSmall.down.obj j).len + 1)) where
  obj a := ULift.up (value a)
  map f := homOfLE (value_le f)

/-- 終頂点関手の nerve を標準単体で表す。 -/
def component (j : AsSmall.{u} SimplexCategory) :
    nerve (Over j) ⟶ (Δ[(AsSmall.down.obj j).len] : SSet.{u}) :=
  nerveMap (functor j) ≫ (stdSimplex.isoNerve (AsSmall.down.obj j).len).inv

/-- 終頂点射は余単体圏の全ての射に自然。 -/
lemma naturality {i j : AsSmall.{u} SimplexCategory} (f : i ⟶ j) :
    nerveMap (Over.map f) ≫ component j =
      component i ≫ stdSimplex.map (AsSmall.down.map f) := by
  apply NatTrans.ext
  funext ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro σ
  apply stdSimplex.ext
  intro k
  rfl

/-- Bousfield–Kan 重みから標準単体の重みへの実際の自然変換。 -/
def weightMap : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} SimplexCategory) ⟶
    AsSmall.down ⋙ SSet.stdSimplex where
  app j := component j
  naturality _ _ f := naturality f

end SerrePositivity.KST.Spectra.CosimplicialLastVertex
