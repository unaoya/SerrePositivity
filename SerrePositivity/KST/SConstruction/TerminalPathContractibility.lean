module
public import SerrePositivity.KST.Spectra.AnodyneMappingLifts
public import SerrePositivity.KST.SConstruction.TerminalPathEvaluation
public import SerrePositivity.KST.Spectra.UnpointedPathEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.ContractibleKan

/-! # 終点固定 path 空間の全境界充填
概要：終点固定 path 空間は Kan 標的に対して可縮 Kan 複体になる。
方針：元の頂点一の包含の anodyne 性と点つき指数の相対持ち上げを使う。
規約：単なる基点での π の消滅でなく全境界の充填を証明。使われ方：向きを保つ homotopy fiber。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 終点基点の区間の基点包含は元の頂点一の anodyne な包含。 -/
lemma terminalPointedInterval_basepoint_anodyne :
    anodyneExtensions terminalPointedInterval.{u}.hom := by
  change anodyneExtensions (Spectra.KanPath.endpoint.{u} 1)
  exact Spectra.KanPath.endpoint_anodyne 1

/-- 終点固定 path 空間の終対象への射は全ての単射に対して RLP を持つ。 -/
lemma terminalPathSpace_terminal_rlp (B : PointedSimplicialSet.{u}) [KanComplex B.right] :
    (MorphismProperty.monomorphisms SSet.{u}).rlp
      (terminal.from (terminalPathSpace B).right) :=
  Spectra.basedHom_terminal_rlp_monomorphisms terminalPointedInterval B
    terminalPointedInterval_basepoint_anodyne

/-- 終点固定 path 空間は全境界を充填できる可縮 Kan 複体。 -/
lemma terminalPathSpace_isContractibleKan (B : PointedSimplicialSet.{u}) [KanComplex B.right] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (terminalPathSpace B).right := by
  intro n b
  let : HasLiftingProperty (boundary.{u} n).ι
      (terminal.from (terminalPathSpace B).right) :=
    terminalPathSpace_terminal_rlp B _ inferInstance
  let sq : CommSq b (boundary.{u} n).ι (terminal.from (terminalPathSpace B).right)
      (terminal.from (Δ[n] : SSet.{u})) := ⟨Subsingleton.elim _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

end SerrePositivity.KST.SConstruction
