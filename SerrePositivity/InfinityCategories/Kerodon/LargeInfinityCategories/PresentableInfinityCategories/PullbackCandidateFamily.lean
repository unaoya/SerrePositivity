module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackVertexCandidates
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.RepresentableRetractions

/-!
概要：二つの小さい対象族の引き戻し候補を、同じ宇宙の小さい型で添字付ける。
方針：局所小ささから標的の同型型を縮小し、指定した同型の持ち上げを評価する。
規約：候補の compact 性と生成性を仮定しない。
使われ方：引き戻しの小さい全部分候補模型の構成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {E D B : SSet.{u + 1}} [Quasicategory B]
  (p : E ⟶ B) (q : D ⟶ B) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsLocallySmall B)
  {AE AD : Type u} (vE : AE → E _⦋0⦌) (vD : AD → D _⦋0⦌)

/-- 概要：二つの小さい対象と像の同型からなる小さい候補の符号型。
方針：各同型型を局所小ささで縮小する。
規約：同型を存在命題に潰さず全ての同型を索引に含める。
使われ方：引き戻しの候補族の小さい添字。 -/
def PullbackCandidateIndex : Type u := by
  have (a : AE) (d : AD) : Small.{u}
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (q.app (Opposite.op ⦋0⦌) (vD d)) (p.app (Opposite.op ⦋0⦌) (vE a))) :=
    hB.vertexIso_small _ _
  exact Σ a : AE, Σ d : AD,
    Shrink.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (q.app (Opposite.op ⦋0⦌) (vD d))
      (p.app (Opposite.op ⦋0⦌) (vE a)))

/-- 概要：小さい候補符号から元の標的の全同型を回収する。
方針：指定された縮小の逆を適用する。
規約：元の両対象を保持する。
使われ方：同値持ち上げへの入力。 -/
def pullbackCandidateIndexIso (t : PullbackCandidateIndex p q hB vE vD) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (q.app (Opposite.op ⦋0⦌) (vD t.2.1))
      (p.app (Opposite.op ⦋0⦌) (vE t.1)) := by
  have (a : AE) (d : AD) : Small.{u}
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (q.app (Opposite.op ⦋0⦌) (vD d)) (p.app (Opposite.op ⦋0⦌) (vE a))) :=
    hB.vertexIso_small _ _
  exact (equivShrink _).symm t.2.2

/-- 概要：小さい符号で索引付けた元の引き戻し内の候補族。
方針：各同型を持ち上げて第一成分の像を第二成分の像に厳密に合わせる。
規約：同じ元の引き戻しを標的とする。
使われ方：小さい全部分模型に用いる対象族。 -/
def pullbackCandidateFamily (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (t : PullbackCandidateIndex p q hB vE vD) : (pullback p q) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackVertexCandidate p q hp (vE t.1) (vD t.2.1)
    (pullbackCandidateIndexIso p q hB vE vD t)).vertex

/-- 概要：候補族の第一成分は指定された元の族の対象と同型。
方針：指定同型の持ち上げの第一成分比較を使う。
規約：頂点の同型を全データで保持する。
使われ方：候補の compact 性の成分判定。 -/
def pullbackCandidateFamily_fstIso (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (t : PullbackCandidateIndex p q hB vE vD) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((pullback.fst p q).app (Opposite.op ⦋0⦌)
      (pullbackCandidateFamily p q hB vE vD hp t)) (vE t.1) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackVertexCandidate p q hp (vE t.1) (vD t.2.1)
    (pullbackCandidateIndexIso p q hB vE vD t)).fstIso

/-- 概要：候補族の第二成分は指定された元の対象そのもの。
方針：同値持ち上げで固定した第二成分を評価する。
規約：同型でなく厳密な一致。
使われ方：候補族の図式と元の表示との比較。 -/
lemma pullbackCandidateFamily_snd (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (t : PullbackCandidateIndex p q hB vE vD) :
    (pullback.snd p q).app (Opposite.op ⦋0⦌)
      (pullbackCandidateFamily p q hB vE vD hp t) = vD t.2.1 :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackVertexCandidate p q hp (vE t.1) (vD t.2.1)
    (pullbackCandidateIndexIso p q hB vE vD t)).snd_eq

/-- 概要：候補族の両射影は、元の族と同じ濃度で compact。
方針：第一成分は指定頂点同型、第二成分は厳密な一致で compact 性を移す。
規約：引き戻し内の compact 性とは区別し、両成分についてのみ主張する。
使われ方：写像空間の引き戻しと filtered 余極限の交換への入力。 -/
lemma pullbackCandidateFamily_components_compact [Quasicategory E] [Quasicategory D]
    {κ : Cardinal.{u}} (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (hvE : ∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (vE a))
    (hvD : ∀ d, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (vD d))
    (t : PullbackCandidateIndex p q hB vE vD) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ
      ((pullback.fst p q).app (Opposite.op ⦋0⦌)
        (pullbackCandidateFamily p q hB vE vD hp t)) ∧
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ
      ((pullback.snd p q).app (Opposite.op ⦋0⦌)
        (pullbackCandidateFamily p q hB vE vD hp t)) := by
  constructor
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_iff_of_iso
      (pullbackCandidateFamily_fstIso p q hB vE vD hp t)).mpr (hvE t.1)
  · rw [pullbackCandidateFamily_snd]
    exact hvD t.2.1

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
