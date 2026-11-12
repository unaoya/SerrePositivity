module

public import SerrePositivity.KST.NonConnective.SequentialEdgePi

/-!
概要：固定 Sp 値関手の端点表示を保つ、同じ二辺の整数 π 作用の比較。
方針：入力の h の等号を写し、同じ端点等式で輸送して既存の BF 比較へ渡す。
規約：入力の数学的構成に依存しない小さい補題に分ける。
使われ方：実 swindle の固定 K 作用の照合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory

/-- 同じ入力射の類の等号を、指定した同じ BF 出力射の全整数 π へ移す。 -/
lemma fixedSpectrumAction_eq {X : SSet.{u + 1}} [Quasicategory X]
    (K : X ⟶ SimplicialNerve OmegaSpectrum.{u}) {x : X _⦋0⦌}
    (f g : X.Edge x x) (P : OmegaSpectrum.{u}) (F G : P ⟶ P)
    (hx : K.app _ x = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex P)
    (hf : ((f.map K).toTruncated).edge =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge F).toTruncated).edge)
    (hg : ((g.map K).toTruncated).edge =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge G).toTruncated).edge)
    (h : Truncated.HomotopyCategory.homMk f.toTruncated =
      Truncated.HomotopyCategory.homMk g.toTruncated) (j : ℤ) :
    OmegaSpectrum.homotopyMap F j = OmegaSpectrum.homotopyMap G j := by
  apply sequentialHomotopyMap_eq_of_homMk_eq
  have h := congrArg ((hoFunctor.map K).toFunctor.map) h
  change Truncated.HomotopyCategory.homMk (f.map K).toTruncated =
    Truncated.HomotopyCategory.homMk (g.map K).toTruncated at h
  have hF := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport hx hx (f.map K).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge F).toTruncated hf
  have hG := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport hx hx (g.map K).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge G).toTruncated hg
  exact hF.symm.trans ((congrArg (fun a ↦
    eqToHom (congrArg HomotopyCategory.mk hx).symm ≫ a ≫
      eqToHom (congrArg HomotopyCategory.mk hx)) h).trans hG)

end SerrePositivity.KST.NonConnective
