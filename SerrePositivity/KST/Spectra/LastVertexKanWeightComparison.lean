module

public import SerrePositivity.KST.Spectra.LastVertexMappingComparison
public import SerrePositivity.KST.Spectra.BousfieldKanWeightLatching
public import SerrePositivity.KST.Spectra.CosimplicialKanReplacement
public import SerrePositivity.KST.Spectra.KanCompositeCancellation

/-!
概要：終頂点の重みの射を実際の Reedy Kan 置換へ送り、各段の全基点 π 同型を示す。
方針：終頂点の anodyne 包含と置換単位を合成し、参照頂点を持つ Kan 複体の合成消去を使う。
規約：置換前の重みが Kan であるとは仮定しない。
使われ方：Goerss–Jardine VII §4。通常 Tot 比較の重みの Whitehead への入力。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.CosimplicialLastVertex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 元の余単体圏での終頂点の重みの自然変換。 -/
def cosimplicialMap : BousfieldKanWeightLatching.weight.{u} ⟶ stdSimplex.{u} where
  app j := component (AsSmall.up.obj j)
  naturality _i _j f := naturality (AsSmall.up.map f)

/-- 終頂点の射の実際の Reedy Kan 置換。 -/
def kanWeightMap : CosimplicialKanReplacement.functor.obj
    BousfieldKanWeightLatching.weight.{u} ⟶
    CosimplicialKanReplacement.functor.obj stdSimplex.{u} :=
  CosimplicialKanReplacement.functor.map cosimplicialMap

/-- 置換した終頂点の射は各段で全基点 π 同型。 -/
lemma kanWeightMap_piIsomorphism (j : SimplexCategory) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (kanWeightMap.{u}.app j) := by
  let : IsIso (terminal.from (Δ[0] : SSet.{u})) :=
    isIso_of_isTerminal stdSimplex.isTerminalObj₀ terminalIsTerminal _
  let : KanComplex (Δ[0] : SSet.{u}) :=
    (modelCategoryQuillen.fibration_iff _).mpr (MorphismProperty.of_isIso _ _)
  let i := overTerminalPoint (AsSmall.up.obj j) ≫
    (CosimplicialKanReplacement.unit.app BousfieldKanWeightLatching.weight.{u}).app j
  let k := simplexTerminalPoint.{u} j.len ≫
    (CosimplicialKanReplacement.unit.app stdSimplex.{u}).app j
  have hi : anodyneExtensions i :=
    anodyneExtensions.comp_mem _ _ (overTerminalPoint_anodyne _)
      (CosimplicialKanReplacement.unit_anodyne _ j)
  have hk : anodyneExtensions k :=
    anodyneExtensions.comp_mem _ _ (simplexTerminalPoint_anodyne _)
      (CosimplicialKanReplacement.unit_anodyne _ j)
  have he : i ≫ kanWeightMap.app j = k := by
    dsimp only [i, k]
    rw [Category.assoc]
    have hn := NatTrans.congr_app (CosimplicialKanReplacement.unit.naturality
      cosimplicialMap.{u}) j
    change cosimplicialMap.app j ≫ (CosimplicialKanReplacement.unit.app stdSimplex).app j =
      (CosimplicialKanReplacement.unit.app BousfieldKanWeightLatching.weight).app j ≫
        kanWeightMap.app j at hn
    rw [← hn, ← Category.assoc]
    change (overTerminalPoint (AsSmall.up.obj j) ≫ component (AsSmall.up.obj j)) ≫ _ = _
    rw [terminalPoint_component]
    rfl
  have hiπ := kanPiIsomorphism_of_anodyne i hi
  have hkπ := kanPiIsomorphism_of_anodyne k hk
  apply (_root_.SerrePositivity.KST.Spectra.KanPiIsomorphism.cancel_left_atVertex hiπ) (x := stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  rw [he]
  exact hkπ

end
end SerrePositivity.KST.Spectra.CosimplicialLastVertex
