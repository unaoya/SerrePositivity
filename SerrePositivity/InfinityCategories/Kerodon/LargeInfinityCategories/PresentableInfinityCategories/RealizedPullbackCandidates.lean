module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackVertexIsoCompatibility
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackCandidateFamily

/-!
概要：実現される基底同型だけを添字として、引き戻しの小さい頂点代表族を構成する。
方針：両成分の小さい代表と基底同型を符号化し、同じ符号の二実現を頂点同型で比較する。
規約：指定同型を保つ頂点持ち上げの追加供給を要求しない。
使われ方：compact 成分の全部分圏の小さい代表族。

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

variable {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
  (p : E ⟶ B) (q : D ⟶ B)

/-- 概要：成分の指定代表を結ぶ元の基底同型。
方針：第二成分の同型を逆に辿り、引き戻しの一致と第一成分の同型を合成する。
規約：第二成分の像から第一成分の像への向き。
使われ方：小さい代表符号の同型成分。 -/
def pullbackComponentIsoCode {x : (pullback p q) _⦋0⦌} {a : E _⦋0⦌} {b : D _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((pullback.fst p q).app _ x) a)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((pullback.snd p q).app _ x) b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (q.app _ b) (p.app _ a) :=
  (d.map q).symm ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackVertexBaseIso p q x ≪≫ e.map p

/-- 概要：同じ成分代表と同じ基底同型を持つ二実現は引き戻し内で同型。
方針：成分比較の商を取り、基底符号の一致から整合条件を得る。
規約：実際の二頂点の間で結論する。
使われ方：一つの符号につき一つの代表を選ぶ正当化。 -/
lemma pullbackComponentIsoCode_same_implies_iso [InnerFibration p]
    {x y : (pullback p q) _⦋0⦌} {a : E _⦋0⦌} {b : D _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((pullback.fst p q).app _ x) a)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((pullback.snd p q).app _ x) b)
    (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((pullback.fst p q).app _ y) a)
    (d' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((pullback.snd p q).app _ y) b)
    (h : pullbackComponentIsoCode p q e d = pullbackComponentIsoCode p q e' d') :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_pullbackVertexIso_of_compatible_components p q (e ≪≫ e'.symm) (d ≪≫ d'.symm)
  have hh := congrArg (fun k ↦ d.map q ≪≫ k ≪≫ (e'.map p).symm) h
  apply Iso.ext
  have hm := congrArg Iso.hom hh
  simpa [pullbackComponentIsoCode, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map, Category.assoc] using hm

variable (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsLocallySmall B) {AE AD : Type u}
  (vE : AE → E _⦋0⦌) (vD : AD → D _⦋0⦌)

/-- 概要：元の引き戻しで実現される小さい成分・基底同型符号。
方針：既存の小さい符号型を、実現の存在命題で制限する。
規約：実現しない基底同型の持ち上げは要求しない。
使われ方：小さい compact 成分代表族の添字。 -/
def RealizedPullbackCandidateIndex : Type u :=
  {t : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackCandidateIndex p q hB vE vD //
    ∃ x : (pullback p q) _⦋0⦌,
      ∃ e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((pullback.fst p q).app _ x) (vE t.1),
      ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((pullback.snd p q).app _ x) (vD t.2.1),
      pullbackComponentIsoCode p q e d = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCandidateIndexIso p q hB vE vD t}

/-- 概要：実現される符号に選んだ元の引き戻しの頂点。
方針：添字が保持する実現の存在から選ぶ。
規約：元の引き戻しを標的とする。
使われ方：小さい代表族の評価。 -/
def realizedPullbackCandidateVertex (t : RealizedPullbackCandidateIndex p q hB vE vD) :
    (pullback p q) _⦋0⦌ := t.property.choose

/-- 概要：選んだ実現の第一成分の指定代表との同型。
方針：同じ実現の存在証明から取り出す。
規約：添字の第一成分を保持する。
使われ方：compact 性と被覆の回収。 -/
def realizedPullbackCandidateFstIso (t : RealizedPullbackCandidateIndex p q hB vE vD) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((pullback.fst p q).app _ (realizedPullbackCandidateVertex p q hB vE vD t))
      (vE t.val.1) := t.property.choose_spec.choose

/-- 概要：選んだ実現の第二成分の指定代表との同型。
方針：同じ実現の存在証明から取り出す。
規約：添字の第二成分を保持する。
使われ方：compact 性と被覆の回収。 -/
def realizedPullbackCandidateSndIso (t : RealizedPullbackCandidateIndex p q hB vE vD) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((pullback.snd p q).app _ (realizedPullbackCandidateVertex p q hB vE vD t))
      (vD t.val.2.1) := t.property.choose_spec.choose_spec.choose

omit [Quasicategory E] [Quasicategory D] in
/-- 概要：選んだ実現の基底符号は指定した同型そのもの。
方針：実現の選択が保持する最後の等式を回収する。
規約：同型の存在への弱化をしない。
使われ方：同じ符号を持つ元の頂点との比較。 -/
lemma realizedPullbackCandidate_code (t : RealizedPullbackCandidateIndex p q hB vE vD) :
    pullbackComponentIsoCode p q (realizedPullbackCandidateFstIso p q hB vE vD t)
      (realizedPullbackCandidateSndIso p q hB vE vD t) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCandidateIndexIso p q hB vE vD t.val :=
  t.property.choose_spec.choose_spec.choose_spec

/-- 概要：両成分が指定族で代表される任意の引き戻し頂点は、小さい実現族の一員と同型。
方針：元の頂点が与える基底同型を縮小して符号を作り、選んだ同符号の実現と比較する。
規約：指定した基底同型を保つ頂点持ち上げの追加仮定を使わない。
使われ方：全 compact 成分を持つ頂点の小さい代表族による被覆。 -/
lemma exists_realizedPullbackCandidate_iso [InnerFibration p]
    (x : (pullback p q) _⦋0⦌)
    (a : AE) (b : AD)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((pullback.fst p q).app _ x) (vE a))
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((pullback.snd p q).app _ x) (vD b)) :
    ∃ t : RealizedPullbackCandidateIndex p q hB vE vD,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x (realizedPullbackCandidateVertex p q hB vE vD t)) := by
  have (a : AE) (b : AD) : Small.{u}
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (q.app (Opposite.op ⦋0⦌) (vD b))
        (p.app (Opposite.op ⦋0⦌) (vE a))) := hB.vertexIso_small _ _
  let code := pullbackComponentIsoCode p q e d
  let t : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackCandidateIndex p q hB vE vD := ⟨a, b, equivShrink _ code⟩
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCandidateIndexIso p q hB vE vD t = code := by
    change (equivShrink _).symm (equivShrink _ code) = code
    exact (equivShrink _).symm_apply_apply code
  let r : RealizedPullbackCandidateIndex p q hB vE vD := ⟨t, x, e, d, ht.symm⟩
  refine ⟨r, pullbackComponentIsoCode_same_implies_iso p q e d
    (realizedPullbackCandidateFstIso p q hB vE vD r)
    (realizedPullbackCandidateSndIso p q hB vE vD r) ?_⟩
  exact ht.symm.trans (realizedPullbackCandidate_code p q hB vE vD r).symm

/-- 概要：元の二族が compact なら、選んだ実現の両成分も同じ濃度で compact。
方針：両成分の指定代表との実際の頂点同型で compact 性を戻す。
規約：引き戻し内の compact 性と成分の compact 性を区別する。
使われ方：小さい実現族を native compact 生成候補へ接続する。 -/
lemma realizedPullbackCandidate_components_compact {μ : Cardinal.{u}}
    (hE : ∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (vE a))
    (hD : ∀ b, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (vD b))
    (t : RealizedPullbackCandidateIndex p q hB vE vD) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
        ((pullback.fst p q).app _ (realizedPullbackCandidateVertex p q hB vE vD t)) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
        ((pullback.snd p q).app _ (realizedPullbackCandidateVertex p q hB vE vD t)) :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_iff_of_iso (realizedPullbackCandidateFstIso p q hB vE vD t)).mpr
      (hE t.val.1),
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_iff_of_iso (realizedPullbackCandidateSndIso p q hB vE vD t)).mpr
      (hD t.val.2.1)⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
