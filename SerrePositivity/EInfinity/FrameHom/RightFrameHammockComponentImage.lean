module

public import SerrePositivity.EInfinity.FrameHom.RightFrameHammockComponent
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative

/-!
概要：実 QCat 比較の選択した逆が同じ元の比較辺の反転と一致することを追跡する。
方針：同じ QCat 同値の指定単位を全ホモトピーとして anodyne 局所化へ送る。
規約：六辺の全自然比較を点ごとの任意の同値と切り離さない。
使われ方：同じ成分比較の単位・零単体公式の合成。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory HomotopicalAlgebra SSet Hammock
open SerrePositivity.Reedy SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel

/-- 概要：同じ QCat 同値の指定逆は anodyne 反転後にも右逆。
方針：元の指定二胞体の全ホモトピーを同じ反転関手に送る。
規約：元の逆と単位を保持。使われ方：六辺の実逆の照合。 -/
lemma qCatEquivalence_hom_inv_Q {A B : SSet.{w}} [Quasicategory A] [Quasicategory B]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence A B) :
    AnodyneHomotopy.anodyneQ.map e.hom ≫ AnodyneHomotopy.anodyneQ.map e.inv = 𝟙 _ := by
  have h := AnodyneHomotopy.map_homotopy_eq AnodyneHomotopy.anodyneQ
    (Localization.inverts _ SSet.anodyneExtensions) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy e.homInvIso.hom)
  simp only [Functor.map_comp] at h
  exact h.trans (AnodyneHomotopy.anodyneQ.map_id _)

/-- 概要：同じ QCat 同値の指定逆は anodyne 反転後にも左逆。
方針：もう一つの指定二胞体を同じ全ホモトピーとして送る。
規約：元の逆と余単位を保持。使われ方：元の反転の一意性。 -/
lemma qCatEquivalence_inv_hom_Q {A B : SSet.{w}} [Quasicategory A] [Quasicategory B]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence A B) :
    AnodyneHomotopy.anodyneQ.map e.inv ≫ AnodyneHomotopy.anodyneQ.map e.hom = 𝟙 _ := by
  have h := AnodyneHomotopy.map_homotopy_eq AnodyneHomotopy.anodyneQ
    (Localization.inverts _ SSet.anodyneExtensions) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy e.invHomIso.hom)
  simp only [Functor.map_comp] at h
  exact h.trans (AnodyneHomotopy.anodyneQ.map_id _)

variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C} [IsCofibrant X]
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
attribute [local instance] rightFrameHammockKanDiagram_kanComplex

include cof in
/-- 概要：同じ実六辺の各成分は anodyne 反転後に同型。
方針：元の実比較の証明済みの弱同値性を使う。
規約：同じ元の辺。使われ方：選択した逆との一意な照合。 -/
lemma rightFrameHammockKanEdge_Q_isIso (i : Fin 6) (Y : AsSmall.{max u v} C) :
    IsIso (AnodyneHomotopy.anodyneQ.map ((rightFrameHammockKanEdge q r i).app Y)) :=
  anodyneQ_map_isIso_of_weak _
    (rightFrameHammockKanEdge_isQCatEquivalence q r cof i Y).isWeakHomotopyEquivalence

include cof in
/-- 概要：選択した実逆の像は同じ元の全自然変換の像の逆に一致する。
方針：同じ指定単位の像と逆の一意性を使う。
規約：元の六辺を保持。使われ方：全族比較と実成分を同じ反転で追跡する。 -/
lemma rightFrameHammockKanEdgeEquivalence_inv_Q (i : Fin 6) (Y : AsSmall.{max u v} C) :
    letI := rightFrameHammockKanEdge_Q_isIso q r cof i Y
    AnodyneHomotopy.anodyneQ.map (rightFrameHammockKanEdgeEquivalence q r cof i Y).inv =
      inv (AnodyneHomotopy.anodyneQ.map ((rightFrameHammockKanEdge q r i).app Y)) := by
  have := rightFrameHammockKanEdge_Q_isIso q r cof i Y
  have h := qCatEquivalence_hom_inv_Q (rightFrameHammockKanEdgeEquivalence q r cof i Y)
  rw [rightFrameHammockKanEdgeEquivalence_hom] at h
  exact (IsIso.inv_eq_of_hom_inv_id
    (f := AnodyneHomotopy.anodyneQ.map ((rightFrameHammockKanEdge q r i).app Y)) h).symm

end SerrePositivity.EInfinity.FrameHom
