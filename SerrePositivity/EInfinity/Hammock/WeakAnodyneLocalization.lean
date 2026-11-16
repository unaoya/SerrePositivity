module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.AnodyneWeakDetection
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanWeakFunctoriality
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead

/-!
# Kan 標的による元の弱同値の anodyne 局所化での可逆性

概要：元の弱ホモトピー同値の同じ射は anodyne 局所化で可逆となる。
方針：連続 Kan 置換後の実際のホモトピー逆を反転し、元の単位を消去する。
規約：元の始終域の Kan 性と単体集合モデル構造は要求しない。
使われ方：モデル構造を使わない元の二重単体集合の対角の弱比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel

lemma anodyneQ_map_isIso_of_homotopyEquivalence {A B : SSet.{u}} (f : A ⟶ B)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f) : IsIso (AnodyneHomotopy.anodyneQ.map f) := by
  obtain ⟨g, ⟨H⟩, ⟨K⟩⟩ := hf
  let Q := AnodyneHomotopy.anodyneQ
  let e : Q.obj A ≅ Q.obj B :=
    { hom := Q.map f
      inv := Q.map g
      hom_inv_id := (Q.map_comp _ _).symm.trans
        ((AnodyneHomotopy.map_homotopy_eq Q SSet.anodyneExtensions.Q_inverts H).trans (Q.map_id _))
      inv_hom_id := (Q.map_comp _ _).symm.trans
        ((AnodyneHomotopy.map_homotopy_eq Q SSet.anodyneExtensions.Q_inverts K).trans
          (Q.map_id _)) }
  exact e.isIso_hom

lemma anodyneQ_map_isIso_of_weak {A B : SSet.{u}} (f : A ⟶ B)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence f) : IsIso (AnodyneHomotopy.anodyneQ.map f) := by
  let Q := AnodyneHomotopy.anodyneQ
  have hR := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacement_map_isWeakHomotopyEquivalence f hf
  have : IsIso (Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f)) :=
    anodyneQ_map_isIso_of_homotopyEquivalence _ hR.isSimplicialHomotopyEquivalence
  have : IsIso (Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app A)) :=
    SSet.anodyneExtensions.Q_inverts _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit_anodyne A)
  have : IsIso (Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app B)) :=
    SSet.anodyneExtensions.Q_inverts _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit_anodyne B)
  have hn := congrArg Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality f)
  change Q.map (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app B) =
    Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map f) at hn
  rw [Q.map_comp, Q.map_comp] at hn
  have hc : IsIso (Q.map f ≫ Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app B)) :=
    hn.symm ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp hc

end SerrePositivity.EInfinity.Hammock
