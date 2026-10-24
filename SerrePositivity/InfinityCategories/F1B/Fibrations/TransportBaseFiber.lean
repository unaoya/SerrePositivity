module

public import SerrePositivity.InfinityCategories.F1B.Fibrations.TransportUniqueness
public import SerrePositivity.InfinityCategories.F1B.Cofinality.CofinalFunctorSpace
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap
public import SerrePositivity.InfinityCategories.Core.EquivalenceFullyFaithful

/-!
概要：基底の終点だけを固定した cocartesian な輸送の比較。
方針：trivial Kan fibration の制限を終点 fiber に移し、ホモトピー圏の充満忠実性を使う。
規約：基底の辺そのものは固定せず、基底の写像空間内の同型に沿って比較する。
使われ方：Kerodon Remark 7.3.1.10 の指定自然変換のホモトピー不変性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：trivial Kan fibration の同じ基底上の fiber への制限も trivial Kan fibration。
方針：元の全境界持ち上げを解き、合成の等式で解を fiber へ戻す。
規約：三つの単体集合には充填性を仮定しない。
使われ方：cocartesian な輸送の空間の終点 fiber での比較。 -/
lemma trivialFibration_vertexFiberMap {E F B : SSet.{u}} (q : E ⟶ F)
    [TrivialKanFibration q] (r : F ⟶ B) (b : B _⦋0⦌) :
    TrivialKanFibration (vertexFiberMap (q ≫ r) r q rfl b) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  have := TrivialKanFibration.mem (p := q) (boundary n).ι inferInstance
  constructor
  intro f g sq
  let m := vertexFiberMap (q ≫ r) r q rfl b
  have hs : CommSq (f ≫ vertexFiberι (q ≫ r) b) (boundary n).ι q
      (g ≫ vertexFiberι r b) := by
    constructor
    rw [Category.assoc, ← vertexFiberMap_ι (q ≫ r) r q rfl b, ← Category.assoc]
    exact congrArg (fun t ↦ t ≫ vertexFiberι r b) sq.w
  let L := vertexFiberLift (q ≫ r) b hs.lift (by
    rw [← Category.assoc, hs.fac_right, Category.assoc, vertexFiberι_comp, SSet.comp_const])
  refine CommSq.HasLift.mk' { l := L, fac_left := ?_, fac_right := ?_ }
  · apply vertexFiber_hom_ext (q ≫ r) b
    rw [Category.assoc, vertexFiberLift_ι]
    exact hs.fac_left
  · apply vertexFiber_hom_ext r b
    change L ≫ (m ≫ vertexFiberι r b) = g ≫ vertexFiberι r b
    rw [vertexFiberMap_ι, ← Category.assoc, vertexFiberLift_ι]
    exact hs.fac_right

/-- 概要：基底の終点を固定した cocartesian な輸送の空間。
方針：可縮な持ち上げの射影と coslice の終点射影の合成の fiber を取る。
規約：基底の辺はこの空間の中で動く。
使われ方：基底の写像空間で同型な辺の輸送を比較する。 -/
def transportBaseFiber {E B : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E)
    (p : E ⟶ B) (b : B _⦋0⦌) : SSet.{u} :=
  vertexFiber (cocartesianCosliceProjection a p ≫ sliceUnderProjection (a ≫ p)) b

/-- 概要：終点固定の輸送を基底の写像空間へ射影する。
方針：cocartesian な持ち上げの射影を fiber へ制限する。
規約：右辺は始点 a≫p と終点 b を固定した写像空間の coslice 模型。
使われ方：基底の辺のホモトピー類による輸送の比較。 -/
def transportBaseFiberMap {E B : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E)
    (p : E ⟶ B) (b : B _⦋0⦌) :
    transportBaseFiber a p b ⟶ vertexFiber (sliceUnderProjection (a ≫ p)) b :=
  vertexFiberMap _ _ (cocartesianCosliceProjection a p) rfl b

/-- 概要：終点固定の輸送の基底写像空間への射影は trivial Kan fibration。
方針：cocartesian な持ち上げの射影の全境界持ち上げを fiber へ制限する。
規約：p は cocartesian fibration。
使われ方：基底のホモトピーに沿う輸送の選択の持ち上げ。 -/
instance transportBaseFiberMap_trivialKanFibration {E B : SSet.{u}}
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) [CocartesianHornFibration p]
    (b : B _⦋0⦌) : TrivialKanFibration (transportBaseFiberMap a p b) :=
  trivialFibration_vertexFiberMap (cocartesianCosliceProjection a p)
    (sliceUnderProjection (a ≫ p)) b

/-- 概要：基底が quasicategory なら終点固定の輸送の空間は Kan 複体。
方針：coslice 射影の fiber の Kan 性を、trivial Kan fibration の全空間へ移す。
規約：p は cocartesian fibration。
使われ方：基底の写像空間内の同型の持ち上げ。 -/
instance transportBaseFiber_kanComplex {E B : SSet.{u}} [Quasicategory B]
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) [CocartesianHornFibration p]
    (b : B _⦋0⦌) : KanComplex (transportBaseFiber a p b) := by
  have := cofinalVertexFiber_kanComplex_of_leftFibration (sliceUnderProjection (a ≫ p)) b
  apply kanComplex_of_rightHornFillers
  intro n i _ f
  let q := transportBaseFiberMap a p b
  obtain ⟨g, hg⟩ := KanComplex.hornFilling (f ≫ q)
  have := TrivialKanFibration.mem (p := q) (horn (n + 1) i).ι inferInstance
  have sq : CommSq f (horn (n + 1) i).ι q g := ⟨hg⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 概要：終点固定の輸送から、元の射の同じ終点上の fiber への評価。
方針：cocartesian な coslice の終点射影を fiber に制限する。
規約：基底の辺は動いてよいが、終点 b は固定する。
使われ方：基底の写像空間内の同型から輸送の終点の同型を得る。 -/
def transportBaseFiberTarget {E B : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E)
    (p : E ⟶ B) (b : B _⦋0⦌) : transportBaseFiber a p b ⟶ vertexFiber p b :=
  vertexFiberMap _ p (cocartesianCosliceι a p ≫ sliceUnderProjection a) (by rfl) b

/-- 概要：基底の写像空間内で同型な持ち上げは、元の終点の fiber 内で同型。
方針：trivial Kan fibration のホモトピー圏の充満忠実性で同型を持ち上げ、終点で評価する。
規約：始点 a と終点 b を固定し、基底の辺そのものの一致は仮定しない。
使われ方：指定自然変換のホモトピー類に関する不変性への一般的な接続。 -/
def transportBaseFiberTargetIso {E B : SSet.{u}} [Quasicategory B]
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) [CocartesianHornFibration p]
    (b : B _⦋0⦌) (t v : (transportBaseFiber a p b) _⦋0⦌)
    (e : VertexIso ((transportBaseFiberMap a p b).app (Opposite.op ⦋0⦌) t)
      ((transportBaseFiberMap a p b).app (Opposite.op ⦋0⦌) v)) :
    VertexIso ((transportBaseFiberTarget a p b).app (Opposite.op ⦋0⦌) t)
      ((transportBaseFiberTarget a p b).app (Opposite.op ⦋0⦌) v) := by
  let q := transportBaseFiberMap a p b
  let hq := (isQCatEquivalence_of_trivialKanFibration q).isFullyFaithful.toHoFullyFaithful
  exact VertexIso.map (hq.preimageIso e) (transportBaseFiberTarget a p b)

/-- 概要：基底の辺を固定した持ち上げを、終点だけを固定した持ち上げの空間へ入れる。
方針：基底の辺の終点の等式を fiber の条件に合成する。
規約：s は基底の辺、hs はその終点が b である条件。
使われ方：具体的な比較錐の輸送を基底ホモトピーの比較へ渡す。 -/
def transportChoiceToBaseFiber {E B : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E)
    (p : E ⟶ B) (s : (sliceUnder (a ≫ p)) _⦋0⦌) (b : B _⦋0⦌)
    (hs : (sliceUnderProjection (a ≫ p)).app (Opposite.op ⦋0⦌) s = b)
    (t : (vertexFiber (cocartesianCosliceProjection a p) s) _⦋0⦌) :
    (transportBaseFiber a p b) _⦋0⦌ := by
  refine ⟨t.val, ?_⟩
  have ht : (cocartesianCosliceProjection a p).app (Opposite.op ⦋0⦌) t.val = s :=
    t.property.trans (pinchedConstant_zero s)
  change (sliceUnderProjection (a ≫ p)).app (Opposite.op ⦋0⦌)
    ((cocartesianCosliceProjection a p).app (Opposite.op ⦋0⦌) t.val) = PinchedHom.constant b 0
  rw [ht, hs, pinchedConstant_zero]

/-- 概要：持ち上げを終点固定の空間へ入れて基底へ射影すると元の基底の辺を得る。
方針：零単体の fiber 条件を使う。
規約：等式は元の coslice の頂点として述べる。
使われ方：具体的な基底のホモトピーとの照合。 -/
lemma transportChoiceToBaseFiber_map_val {E B : SSet.{u}}
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B)
    (s : (sliceUnder (a ≫ p)) _⦋0⦌) (b : B _⦋0⦌)
    (hs : (sliceUnderProjection (a ≫ p)).app (Opposite.op ⦋0⦌) s = b)
    (t : (vertexFiber (cocartesianCosliceProjection a p) s) _⦋0⦌) :
    ((transportBaseFiberMap a p b).app (Opposite.op ⦋0⦌)
      (transportChoiceToBaseFiber a p s b hs t)).val = s :=
  t.property.trans (pinchedConstant_zero s)

end SerrePositivity.InfinityCategories
