module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.MappingSpacePullback
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence

/-!
概要：充満忠実な inner fibration の基底変換。
方針：右 pinched 写像空間の境界を元の射の写像空間で持ち上げ、引き戻しに戻す。
規約：基底変換に使う射には単射性を仮定しない。
使われ方：Kerodon §4.8.3（Tag 05AW） の標準単体への還元。

対応節は Kerodon 4.8（Tag 0578）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors

/-- 概要：引き戻しの第二成分の写像空間から元の標的の写像空間への射。
方針：後合成で写し、引き戻しの一致条件で端点の表示を合わせる。
規約：端点は第一成分の像で表示する。
使われ方：Kerodon §4.8.4（Tag 06SQ） の写像空間の基底変換。 -/
noncomputable def pinchedHomPullbackBaseMap {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom ((pullback.snd p q).app (Opposite.op ⦋0⦌) v)
      ((pullback.snd p q).app (Opposite.op ⦋0⦌) w) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (p.app (Opposite.op ⦋0⦌) ((pullback.fst p q).app (Opposite.op ⦋0⦌) v))
      (p.app (Opposite.op ⦋0⦌) ((pullback.fst p q).app (Opposite.op ⦋0⦌) w)) where
  app n := by
    obtain ⟨⟨d⟩⟩ := n
    exact ↾(fun x ↦ ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedSimplexMap q x).val,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedSimplexMap q x).source.trans
        (congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z d) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_compat p q v).symm),
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedSimplexMap q x).target.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_compat p q w).symm⟩)
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    intro x
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
    change q.app (Opposite.op ⦋m + 1⦌) (Y.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α.unop).op x.val) =
      B.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α.unop).op (q.app (Opposite.op ⦋n + 1⦌) x.val)
    exact ConcreteCategory.congr_hom (q.naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α.unop).op) x.val

/-- 概要：引き戻しの写像空間の両成分は標的の写像空間で一致する。
方針：各 pinched 単体の値を引き戻しの可換性で比較する。
規約：端点の一致は BaseMap に含める。
使われ方：Kerodon §4.8.4（Tag 06SQ） の相対的な境界充填。 -/
lemma pinchedHomPullbackBaseMap_comm {X Y B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)
    (v w : (pullback p q) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (pullback.fst p q) v w ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p ((pullback.fst p q).app (Opposite.op ⦋0⦌) v)
          ((pullback.fst p q).app (Opposite.op ⦋0⦌) w) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (pullback.snd p q) v w ≫ pinchedHomPullbackBaseMap p q v w := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro x
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pullbackSimplex_compat p q x.val

/-- 概要：充満忠実な inner fibration の基底変換の写像空間の射は trivial Kan fibration。
方針：元の写像空間の射の境界持ち上げを取り、第二成分と合わせて引き戻しへ戻す。
規約：基底変換の始域 Y の quasicategory 性は不要。
使われ方：Kerodon §4.8.3（Tag 05AW） の相対的な境界の充填。 -/
lemma IsFullyFaithful.pinchedHomMap_pullback_snd_trivialKanFibration {X Y B : SSet.{u}}
    [Quasicategory X] [Quasicategory B] {p : X ⟶ B} [InnerFibration p]
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful p) (q : Y ⟶ B) (v w : (pullback p q) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (pullback.snd p q) v w) := by
  let mx := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (pullback.fst p q) v w
  let my := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (pullback.snd p q) v w
  let mp := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p ((pullback.fst p q).app (Opposite.op ⦋0⦌) v)
    ((pullback.fst p q).app (Opposite.op ⦋0⦌) w)
  let mq := pinchedHomPullbackBaseMap p q v w
  have hm : mx ≫ mp = my ≫ mq := pinchedHomPullbackBaseMap_comm p q v w
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration mp := hp.pinchedHomMap_trivialKanFibration _ _
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := mp) (boundary n).ι inferInstance
  constructor
  intro a b sq
  have hw : (a ≫ mx) ≫ mp = (boundary n).ι ≫ (b ≫ mq) := by
    rw [Category.assoc, hm, ← Category.assoc a my mq, sq.w, Category.assoc]
  let t : CommSq (a ≫ mx) (boundary n).ι mp (b ≫ mq) := ⟨hw⟩
  have hc : ∀ (d : ℕ) (z : (Δ[n] : SSet.{u}) _⦋d⦌),
      p.app (Opposite.op ⦋d + 1⦌) (t.lift.app (Opposite.op ⦋d⦌) z).val =
        q.app (Opposite.op ⦋d + 1⦌) (b.app (Opposite.op ⦋d⦌) z).val := by
    intro d z
    exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.val
      (ConcreteCategory.congr_hom (NatTrans.congr_app t.fac_right (Opposite.op ⦋d⦌)) z)
  let l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomPullbackLift p q v w t.lift b hc
  have hmx : l ≫ mx = t.lift := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomPullbackLift_fst _ _ _ _ _ _ _
  have hmy : l ≫ my = b := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomPullbackLift_snd _ _ _ _ _ _ _
  refine CommSq.HasLift.mk' { l := l, fac_left := ?_, fac_right := hmy }
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomPullback_hom_ext p q v w
  · rw [Category.assoc, hmx]
    exact t.fac_left
  · rw [Category.assoc, hmy]
    exact sq.w.symm

/-- 概要：充満忠実な inner fibration の quasicategory への基底変換は充満忠実。
方針：基底変換の写像空間の射の trivial Kan fibration 性からホモトピー逆を構成する。
規約：元の始域・終域と基底変換の始域が quasicategory。
使われ方：Kerodon §4.8.3（Tag 05AW） の標準単体への還元。 -/
lemma IsFullyFaithful.pullback_snd {X Y B : SSet.{u}}
    [Quasicategory X] [Quasicategory B] [Quasicategory Y] {p : X ⟶ B} [InnerFibration p]
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful p) (q : Y ⟶ B) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (pullback.snd p q) := by
  have : InnerFibration (pullback.snd p q) :=
    ⟨innerFibrations.pullback_snd p q (InnerFibration.mem (q := p))⟩
  have : Quasicategory (pullback p q) := quasicategory_of_innerFibration (pullback.snd p q)
  intro v w
  have := hp.pinchedHomMap_pullback_snd_trivialKanFibration q v w
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
