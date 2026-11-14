module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftAnodynePushoutProduct
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeOuterHornOp
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：cofinality を検査する底上の関手空間とその制限。
方針：後合成の頂点 fiber を直接取り、left anodyne に沿う制限の全境界を充填する。
規約：F1.RelativeFunctorSpace は LeftFiberKan 経由で LeftUnstraightening を import するため、
ここでは F1 の一般の fiber・前合成・境界充填の証明だけを同じ定義で再構成する。
F1 のファイルは変更せず、名前を cofinalFunctor に分けて両方を import しても衝突しない。
使われ方：Kerodon Definition 7.2.1.1（Tag 02N1）、Proposition 7.2.1.3（Tag 02N3）、straightening 非依存の B3。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：底図式 a に厳密に重なる関手空間。
方針：後合成の内部 Hom の指定頂点 fiber を取る。
規約：F1.relativeFunctorSpace と同じ構成。import の範囲のみを狭める。
使われ方：Kerodon Definition 7.2.1.1（Tag 02N1） の相対関手空間。 -/
@[kerodon 02N1]
def cofinalFunctorSpace {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)

/-- 概要：全ての左ホーンを充填できる単体集合は Kan 複体。
方針：反転した単体集合の右ホーンを充填し、その全ホーン充填を元に戻す。
規約：左ホーンは正次元で最後の添字以外を持つ。
使われ方：Kerodon Corollary 4.4.2.3（Tag 019E）、left fibration の fiber の Kan 判定。 -/
lemma cofinalKanComplex_of_leftHornFillers (X : SSet.{u})
    (hf : ∀ (n : ℕ) (i : Fin (n + 2)), i < n + 1 →
      ∀ σ : (horn (n + 1) i : SSet.{u}) ⟶ X,
        ∃ F : (Δ[n + 1] : SSet.{u}) ⟶ X, (horn (n + 1) i).ι ≫ F = σ) : KanComplex X := by
  have : KanComplex X.op := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanComplex_of_rightHornFillers
    intro n i hi σ
    have hir : i.rev < n + 1 := by
      rw [Fin.val_rev]
      change 0 < i.val at hi
      omega
    let τ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap (n + 1) i σ ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom
    obtain ⟨F, hF⟩ := hf n i.rev hir τ
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornFiller_of_reverseHornFiller (n + 1) i σ
      (F ≫ (SSet.opFunctorCompOpFunctorIso.app X).inv)
    rw [← Category.assoc, hF]
    dsimp only [τ]
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanComplex_of_rightHornFillers
  intro n i _ σ
  obtain ⟨F, hF⟩ := KanComplex.hornFilling (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseHornMap (n + 1) i σ)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.hornFiller_of_reverseHornFiller (n + 1) i σ F hF.symm

/-- 概要：left fibration の頂点上の fiber は Kan 複体。
方針：fiber の左ホーンを元へ含め、下を定値にして持ち上げ、fiber へ戻す。
規約：元と底の quasicategory 性は不要。
使われ方：Kerodon Corollary 4.4.2.3（Tag 019E）、相対関手空間の Kan 性。 -/
lemma cofinalVertexFiber_kanComplex_of_leftFibration {E B : SSet.{u}} (p : E ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (b : B _⦋0⦌) : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) := by
  apply cofinalKanComplex_of_leftHornFillers
  intro n i hi a
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions.intro i hi)
  have sq : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) (horn (n + 1) i).ι p (SSet.const b) := by
    constructor
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, SSet.comp_const]
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b sq.lift sq.fac_right, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
  exact sq.fac_left

/-- 概要：left fibration への相対関手空間は Kan 複体。
方針：内部 Hom の left fibration 性と頂点 fiber の Kan 性を合わせる。
規約：底の quasicategory 性は不要。
使われ方：Kerodon Definition 7.2.1.1（Tag 02N1） のホモトピー同値の検査。 -/
instance cofinalFunctorSpace_kanComplex {A E B : SSet.{u}} (p : E ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (a : A ⟶ B) : KanComplex (cofinalFunctorSpace p a) :=
  cofinalVertexFiber_kanComplex_of_leftFibration ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)

/-- 概要：パラメータ始域の射は底を引き戻した相対関手単体集合への前合成を与える。
方針：内部 Hom の前合成の自然性を用いて fiber へ持ち上げる。
規約：p と i の充填性や単射性は不要。
使われ方：Kerodon §5.3.1（Tag 035D）、undercategory の反変性からの共変 transport。 -/
def cofinalFunctorPre {A D E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A) :
    cofinalFunctorSpace p a ⟶ cofinalFunctorSpace p (i ≫ a) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _ ≫ (pre i).app E) (by
    rw [Category.assoc, ← (pre i).naturality p, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp]
    rfl)

/-- 概要：相対前合成の包含後の射は通常の内部 Hom の前合成。
方針：fiber への持ち上げの定義を計算する。
規約：底の図式は i≫a。
使われ方：Kerodon §5.3.1（Tag 035D）、相対前合成の等式の検査。 -/
lemma cofinalFunctorPre_ι {A D E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A) :
    cofinalFunctorPre p a i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom D).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ a)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) ≫ (pre i).app E := rfl

/-- 概要：相対前合成は恒等射を恒等射へ写す。
方針：fiber の包含後に内部 Hom の恒等則を使う。
規約：固定図式の等式は単体集合の合成の定義に沿って同定する。
使われ方：Kerodon §5.3.1（Tag 035D）、strict transport の関手の単位則。 -/
lemma cofinalFunctorPre_id {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) :
    cofinalFunctorPre p a (𝟙 A) = 𝟙 (cofinalFunctorSpace p a) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) ≫ (pre (𝟙 A)).app E =
    𝟙 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
  rw [pre_id, NatTrans.id_app, Category.comp_id, Category.id_comp]

/-- 概要：相対前合成は射の合成を逆順の前合成へ写す。
方針：fiber の包含後に内部 Hom の前合成の合成則を使う。
規約：i の後に j で制限する合成は j≫i による制限。
使われ方：Kerodon §5.3.1（Tag 035D）、strict transport の関手の合成則。 -/
lemma cofinalFunctorPre_comp {A D T E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A) (j : T ⟶ D) :
    cofinalFunctorPre p a i ≫ cofinalFunctorPre p (i ≫ a) j =
      cofinalFunctorPre p a (j ≫ i) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom T).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((j ≫ i) ≫ a))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) ≫ (pre i).app E) ≫
      (pre j).app E = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) ≫ (pre (j ≫ i)).app E
  rw [Category.assoc, ← NatTrans.comp_app, ← pre_map]

/-- 概要：left anodyne な射による相対前合成は trivial Kan fibration。
方針：底を固定した持ち上げ問題を相対内部 Hom に入れて解き、再び fiber へ戻す。
規約：元の射 p の left fibration 性だけを要求する。
使われ方：Kerodon §5.3.1（Tag 035D）、始対象の nerve の頂点包含に沿う制限。 -/
lemma cofinalFunctorPre_trivialKanFibration {A D E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (a : A ⟶ B) (i : D ⟶ A)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (cofinalFunctorPre p a i) := by
  let sq' := CategoryTheory.Functor.PullbackObjObj.ofHasPullback internalHom i p
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.trivialKanFibration_relativeHom_of_leftAnodyne i hi p sq'
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := sq'.π) (boundary n).ι inferInstance
  constructor
  intro u v sq
  let ιA := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
  let ιD := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom D).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ a))
  let V : (Δ[n] : SSet.{u}) ⟶ sq'.pt :=
    sq'.isPullback.lift (v ≫ ιD) (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)) (by
      change (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom D).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ a))) ≫
        (ihom D).map p = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) ≫ (pre i).app B
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, SSet.const_comp]
      rfl)
  have hVfst : V ≫ sq'.fst = v ≫ ιD := sq'.isPullback.lift_fst _ _ _
  have hVsnd : V ≫ sq'.snd = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) := sq'.isPullback.lift_snd _ _ _
  have hs : CommSq (u ≫ ιA) (boundary n).ι sq'.π V := by
    constructor
    apply sq'.hom_ext
    · simp only [Category.assoc, sq'.π_fst, hVfst]
      change (u ≫ ιA) ≫ (pre i).app E = ((boundary n).ι ≫ v) ≫ ιD
      exact (congrArg (fun q ↦ q ≫ ιD) sq.w).trans (by rfl)
    · simp only [Category.assoc, sq'.π_snd, hVsnd]
      change (u ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)) ≫ (ihom A).map p = _
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, SSet.comp_const]
  have hbase : hs.lift ≫ (ihom A).map p = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) := by
    calc
      _ = (hs.lift ≫ sq'.π) ≫ sq'.snd := by
        rw [Category.assoc]
        exact congrArg (fun q ↦ hs.lift ≫ q) sq'.π_snd.symm
      _ = V ≫ sq'.snd := congrArg (fun q ↦ q ≫ sq'.snd) hs.fac_right
      _ = _ := hVsnd
  let W := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) hs.lift hbase
  refine CommSq.HasLift.mk' { l := W, fac_left := ?_, fac_right := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
    change ((boundary n).ι ≫ W) ≫ ιA = u ≫ ιA
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    exact hs.fac_left
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom D).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ a))
    rw [Category.assoc, cofinalFunctorPre_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    change hs.lift ≫ (pre i).app E = v ≫ ιD
    calc
      _ = (hs.lift ≫ sq'.π) ≫ sq'.fst := by
        rw [Category.assoc]
        exact congrArg (fun q ↦ hs.lift ≫ q) sq'.π_fst.symm
      _ = V ≫ sq'.fst := congrArg (fun q ↦ q ≫ sq'.fst) hs.fac_right
      _ = _ := hVfst

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "4.1.1.2"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace
