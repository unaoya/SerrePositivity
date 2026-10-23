module

public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationMappingSpaces
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorInverse
public import SerrePositivity.InfinityCategories.F1.Coherent.EnrichedHomotopy

/-!
概要：底上の left fibrations の前合成同値を、その coherent nerve の可逆な辺へ移す。
方針：底を固定した逆射と二つの相対比較を豊穣 Hom 内の逆条件として使う。
規約：底の quasicategory 性を仮定し、比較は元の底上の射そのものについて述べる。
使われ方：Kerodon Corollary 5.6.0.6、全空間の同値を fibration の ∞ 圏内の同値にする。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：left fibrations の通常の射の豊穣表示は対応する相対関手の頂点。
方針：相対 Hom の単位からの射と零単体の全単射の往復を計算する。
規約：p と q は束縛した left fibration の対象。
使われ方：Kerodon §2.4.3、相対的な逆条件を coherent な逆条件へ移す。 -/
lemma leftFibrationHom_vertex {B : SSet.{u}} (p q : LeftFibrationObject B) (f : p ⟶ q) :
    SimplicialCategory.homEquiv' p q f =
      relativeFunctorVertex q.val.hom p.val.hom f.left f.w := by
  change (SSet.unitHomEquiv _) ((SSet.unitHomEquiv _).symm
    ((relativeFunctorVertexEquiv q.val.hom p.val.hom) ((overHomEquivSubtype p.val q.val) f))) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- 概要：底上の left fibrations の前合成同値は fibration の coherent nerve の可逆な辺。
方針：相対逆の二つの比較を豊穣 Hom の頂点で表し、一般の coherent な逆射の判定を使う。
規約：指定した射 f から作った辺の可逆性。
使われ方：Kerodon Corollary 5.6.0.6、復元比較の全空間の同値を ∞ 圏の辺として扱う。 -/
lemma leftFibrationInfinityEdge_isInvertible_of_precompositionEquivalence
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f) :
    IsInvertibleEdge (leftFibrationInfinityEdge p q f hf) := by
  obtain ⟨g, hg, ⟨hu⟩, ⟨hc⟩⟩ := exists_relativeFunctorInverse_of_precompositionEquivalence p q f hf ef
  apply coherentNerveEdge_isInvertible_of_enrichedInverse
    (show leftFibrationObjectOf p ⟶ leftFibrationObjectOf q from Over.homMk f hf)
    (show leftFibrationObjectOf q ⟶ leftFibrationObjectOf p from Over.homMk g hg)
  · rw [leftFibrationHom_vertex, leftFibrationHom_vertex]
    exact hu
  · rw [leftFibrationHom_vertex, leftFibrationHom_vertex]
    exact hc

/-- 概要：底上の前合成同値は left fibrations の ∞ 圏の二つの頂点の同型を与える。
方針：構成した可逆な辺のホモトピー圏の射を同型にする。
規約：同型の順方向は指定した底上の射の辺の類。
使われ方：Kerodon Corollary 5.6.0.6、復元比較を straightening の coherent な写像で送る。 -/
noncomputable def leftFibrationInfinityVertexIsoOfPrecompositionEquivalence
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (ef : IsPrecompositionEquivalence f) :
    VertexIso (leftFibrationInfinityVertex p) (leftFibrationInfinityVertex q) := by
  letI : IsIso (SSet.Truncated.HomotopyCategory.homMk
      (leftFibrationInfinityEdge p q f hf).toTruncated) :=
    leftFibrationInfinityEdge_isInvertible_of_precompositionEquivalence p q f hf ef
  exact asIso (SSet.Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated)

end SerrePositivity.InfinityCategories
