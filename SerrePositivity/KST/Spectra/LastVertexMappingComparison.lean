module

public import SerrePositivity.KST.Spectra.NerveTerminalPointAnodyne
public import SerrePositivity.KST.Spectra.AnodynePointMappingComparison
public import SerrePositivity.KST.Spectra.CosimplicialLastVertex

/-!
概要：終頂点の重みの射は Kan 標的への指数で各段の全基点 π 同型を誘導する。
方針：over 圏の恒等射の頂点と標準単体の終頂点はともに anodyne な包含であり、比較射はそれらを保つ。
規約：非 Kan な重みの間の単一の逆向きホモトピーを要求しない。
使われ方：Goerss–Jardine VII §4。Reedy cofibrant な重みの比較の対象ごとの入力。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalClosed SSet
open scoped MonoidalClosed Simplicial

namespace SerrePositivity.KST.Spectra.CosimplicialLastVertex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 有限順序圏の最後の頂点は終対象。 -/
def ordinalTerminal (n : ℕ) :
    IsTerminal (ULift.up (Fin.last n) : ULift.{u} (Fin (n + 1))) :=
  IsTerminal.ofUniqueHom (fun x ↦ homOfLE (Fin.le_last x.down))
    (fun _ _ ↦ Subsingleton.elim _ _)

/-- 標準零単体から標準 n 単体の終頂点への実際の包含。 -/
def simplexTerminalPoint (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ Δ[n] :=
  NerveTerminalPoint.inclusion (ULift.up (Fin.last n) : ULift.{u} (Fin (n + 1))) ≫
    (stdSimplex.isoNerve n).inv

/-- 標準単体の終頂点包含は anodyne。 -/
lemma simplexTerminalPoint_anodyne (n : ℕ) :
    anodyneExtensions (simplexTerminalPoint.{u} n) :=
  anodyneExtensions.comp_mem _ _ (NerveTerminalPoint.anodyne (ordinalTerminal n))
    (anodyneExtensions.of_isIso _)

/-- over 圏の恒等射が与える標準の終頂点包含。 -/
def overTerminalPoint (j : AsSmall.{u} SimplexCategory) :
    (Δ[0] : SSet.{u}) ⟶ nerve (Over j) :=
  NerveTerminalPoint.inclusion (Over.mk (𝟙 j))

/-- over 圏の恒等射への頂点包含は anodyne。 -/
lemma overTerminalPoint_anodyne (j : AsSmall.{u} SimplexCategory) :
    anodyneExtensions (overTerminalPoint j) :=
  NerveTerminalPoint.anodyne (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 j)))

/-- 実際の終頂点比較射は指定した終頂点包含と厳密に可換。 -/
lemma terminalPoint_component (j : AsSmall.{u} SimplexCategory) :
    overTerminalPoint j ≫ component j =
      simplexTerminalPoint (AsSmall.down.obj j).len := by
  apply NatTrans.ext
  funext ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro σ
  apply stdSimplex.ext
  intro k
  rfl

/-- 終頂点の重みの射への前合成は全ての Kan 標的で全基点 π 同型。 -/
lemma component_pre_piIsomorphism (j : AsSmall.{u} SimplexCategory)
    (Y : SSet.{u}) [KanComplex Y] : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((pre (component j)).app Y) :=
  pre_piIsomorphism_of_commonAnodyne (overTerminalPoint j)
    (simplexTerminalPoint (AsSmall.down.obj j).len)
    (overTerminalPoint_anodyne j) (simplexTerminalPoint_anodyne _)
    (component j) (terminalPoint_component j) Y

end
end SerrePositivity.KST.Spectra.CosimplicialLastVertex
