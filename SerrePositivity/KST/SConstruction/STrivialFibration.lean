module
public import SerrePositivity.KST.SConstruction.SOneExact
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction
public import Mathlib.Tactic.CrossRefAttribute

/-! # S 構成による trivial Kan fibration の保存
概要：自明ファイブレーションによる後合成は gapped 条件を反映し、全 S_n で自明ファイブレーションを誘導する。
方針：内部 Hom の持ち上げを全部分複体へ制限する。
規約：源と標的は quasicategory。使われ方：経路の比較の反復 S への移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：内部 Hom の標的の自明ファイブレーションは自明ファイブレーションを誘導する。
方針：テンソルが単射を保つことと閉随伴の持ち上げ同値を使う。
規約：対象の Kan 性は不要。使われ方：図式全体の持ち上げ。 -/
@[kerodon 0071]
instance ihomMap_trivialKanFibration (K : SSet.{u}) {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((ihom K).map p) where
  mem := by
    intro A B i hi
    let : Mono i := hi
    have hl : HasLiftingProperty ((tensorLeft K).map i) p :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem ((tensorLeft K).map i) inferInstance
    exact ((ihom.adjunction K).hasLiftingProperty_iff i p).mp hl

/-- 概要：全部分複体の頂点条件を反映する自明ファイブレーションは制限後も自明ファイブレーション。
方針：底の持ち上げの各頂点の条件を標的の条件から反映する。
規約：条件の保存は指定した制限射の可換式に含む。使われ方：gapped 図式への制限。 -/
lemma fullSubcomplex_trivialKanFibration_of_reflects {X Y : SSet.{u}}
    (P : X _⦋0⦌ → Prop) (Q : Y _⦋0⦌ → Prop) (p : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p]
    (q : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y Q)
    (hq : q ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y Q).ι = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι ≫ p)
    (href : ∀ x, Q (p.app (Opposite.op ⦋0⦌) x) → P x) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q where
  mem := by
    intro A B i hi
    let : Mono i := hi
    constructor
    intro a b sq
    let hs : CommSq (a ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι) i p
        (b ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y Q).ι) := ⟨by
      rw [Category.assoc, ← hq, ← Category.assoc, sq.w, Category.assoc]⟩
    let : HasLiftingProperty i p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem i hi
    let l := hs.lift
    let l' := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P l (by
      intro v
      apply href
      have he := ConcreteCategory.congr_hom (NatTrans.congr_app hs.fac_right (Opposite.op ⦋0⦌)) v
      change p.app (Opposite.op ⦋0⦌) (l.app (Opposite.op ⦋0⦌) v) =
        (b.app (Opposite.op ⦋0⦌) v).val at he
      rw [he]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (b.app (Opposite.op ⦋0⦌) v))
    refine CommSq.HasLift.mk' { l := l', fac_left := ?_, fac_right := ?_ }
    · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι).mp
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
      exact hs.fac_left
    · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y Q).ι).mp
      rw [Category.assoc, hq, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
      exact hs.fac_right

/-- 概要：自明ファイブレーションによる後合成は gapped 条件を保存し反映する。
方針：対角の零対象性と全四角形の押し出し性の保存・反映を使う。
規約：安定性は不要。使われ方：S 構成の図式の持ち上げの頂点条件。 -/
lemma isGapped_iff_postcomp_of_trivialKanFibration {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p]
    {n : ℕ} (F : arNerve n ⟶ E) : IsGapped F ↔ IsGapped (F ≫ p) := by
  constructor
  · intro h
    constructor
    · intro i
      exact (isZeroVertex_iff_of_trivialKanFibration p _).mp (h.1 i)
    · intro i j k l hij hjk hkl
      exact (isPushoutSquare_iff_postcomp_of_trivialKanFibration p _).mp (h.2 i j k l hij hjk hkl)
  · intro h
    constructor
    · intro i
      exact (isZeroVertex_iff_of_trivialKanFibration p _).mpr (h.1 i)
    · intro i j k l hij hjk hkl
      exact (isPushoutSquare_iff_postcomp_of_trivialKanFibration p _).mpr (h.2 i j k l hij hjk hkl)

/-- 概要：S_n の後合成は自明ファイブレーションを保つ。
方針：内部 Hom の持ち上げを gapped 条件の反映で全部分複体へ制限する。
規約：hf は既存の後合成射に含まれる保存条件。使われ方：経路の第一行比較の反復。
-/
instance sPostcompCofiber_trivialKanFibration (n : ℕ) {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p]
    (hf : PreservesCofiberData p) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (sPostcompCofiber n p hf) := by
  apply fullSubcomplex_trivialKanFibration_of_reflects
    (fun v => IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) E).symm v))
    (fun v => IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) B).symm v))
    ((ihom (arNerve n)).map p) (sPostcompCofiber n p hf) (sPostcompCofiber_ι n p hf)
  intro v hv
  let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) E).symm v
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F = v := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ E).apply_symm_apply v
  rw [← he] at hv
  change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) B).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F ≫ p))) at hv
  change IsGapped ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) B).symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (arNerve n) B) (F ≫ p))) at hv
  rw [Equiv.symm_apply_apply] at hv
  exact (isGapped_iff_postcomp_of_trivialKanFibration p F).mpr hv

end SerrePositivity.KST.SConstruction
