module
public import SerrePositivity.KST.Fibration.Relative.ClosedRealizationPullback
public import SerrePositivity.KST.Fibration.Relative.ClosedZeroFlag
public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClasses

/-!
概要：指定零旗上の相対 fiber と F(P) の条件付き同型。
方針：Segal 四角形の標準比較と、可縮な底への指定点の基底変換を合成する。
規約：唯一の未供給入力は全旗自然性の Prop。使われ方：K-B の供給を代入して S1 を閉じる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Comparison
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration.Relative

/-- 概要：元の相対実現における指定零旗。
方針：P の指定零旗を同じ包含で送る。
規約：基点を変更しない。使われ方：実 fiber 模型。 -/
def closedRelativeBasepoint {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    (Δ[0] : SSet.{u}) ⟶ closedRelativeRealization P :=
  closedKernelZeroFlag P ≫ closedKernelRealizationPost P

/-- 概要：元の c_B の同じ零旗上の homotopy fiber。
方針：既存の関手的 Kan 分解の引き戻し。
規約：元の c_B を保持。使われ方：K-cof が消費する右辺。 -/
def closedRelativeFiber {B : StableModel.{u}} (P : ClosedStablePredicate B) : SSet.{u} :=
  homotopyPullbackObject (closedRelativeConstant P) (closedRelativeBasepoint P)

/-- 概要：同じ fiber から元の F(B) への射影。
方針：指定引き戻しの第一射影。
規約：局所化前の射。使われ方：包含の回収公式。 -/
def closedRelativeFiberProjection {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    closedRelativeFiber P ⟶ coreSRealizationFunctor.obj B := pullback.fst _ _

/-- 概要：指定零旗の fiber から可縮な全旗を底とする引き戻しへの元の射。
方針：元の cospan の三入力の比較。
規約：左成分は恒等射。使われ方：指定点での基底変換。 -/
def closedRelativeFiberPointMap {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    closedRelativeFiber P ⟶
      homotopyPullbackObject (closedRelativeConstant P) (closedKernelRealizationPost P) :=
  homotopyPullbackMap (𝟙 _) (closedKernelZeroFlag P) (𝟙 _)
    (by simp) (by simp [closedRelativeBasepoint])

/-- 概要：指定点による同じ基底変換は局所化同型。
方針：三入力不変性に全旗の指定点の可逆性を代入。
規約：有限旗自然性の仮定は不要。使われ方：fiber 同型の第二成分。 -/
theorem closedRelativeFiberPointMap_isIso {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    IsIso (AnodyneHomotopy.anodyneQ.map (closedRelativeFiberPointMap P)) :=
  homotopyPullbackMap_localized_isIso (𝟙 _) (closedKernelZeroFlag P) (𝟙 _)
    (by simp) (by simp [closedRelativeBasepoint]) (by infer_instance)
    (specifiedPoint_isIso _ (closedKernelRealization_toPoint_isIso P)) (by infer_instance)

/-- 概要：有限旗自然性を唯一の明示仮定とする要求の fiber 同型。
方針：Segal 四角形の比較と指定零旗の比較の逆を合成。
規約：商・Verdier 列・完備化・共終性の仮定なし。使われ方：S1 の公開本体。 -/
def closedRelativeFiberIso {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (h : ClosedStableFlagPostPullback P) :
    AnodyneHomotopy.anodyneQ.obj (coreSRealizationFunctor.obj (closedStableModel P)) ≅
      AnodyneHomotopy.anodyneQ.obj (closedRelativeFiber P) := by
  have hp : IsHomotopyPullback (closedRelativeSquare P).flip :=
    (isHomotopyPullback_flip_iff _).2 (closedRelativeSquare_homotopyPullback P h)
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (homotopyPullbackComparison (closedRelativeSquare P).flip)) := hp
  have := closedRelativeFiberPointMap_isIso P
  exact asIso (AnodyneHomotopy.anodyneQ.map
    (homotopyPullbackComparison (closedRelativeSquare P).flip)) ≪≫
      (asIso (AnodyneHomotopy.anodyneQ.map (closedRelativeFiberPointMap P))).symm

/-- 概要：同型の順射と射影は元の P 包含の F 像。
方針：二つの元の比較射の第一射影公式を照合する。
規約：指定 fiber と指定包含のまま。使われ方：K-cof への射の同定。 -/
theorem closedRelativeFiberIso_projection {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (h : ClosedStableFlagPostPullback P) :
    (closedRelativeFiberIso P h).hom ≫
      AnodyneHomotopy.anodyneQ.map (closedRelativeFiberProjection P) =
        AnodyneHomotopy.anodyneQ.map (coreSRealizationFunctor.map (closedStableInclusion P)) := by
  let Q := AnodyneHomotopy.anodyneQ
  let π := pullback.fst (closedRelativeConstant P)
    (AnodyneKanReplacement.factorization.p.app (Arrow.mk (closedKernelRealizationPost P)))
  have hm : closedRelativeFiberPointMap P ≫ π = closedRelativeFiberProjection P := by
    exact (homotopyPullbackMap_fst (𝟙 _) (closedKernelZeroFlag P) (𝟙 _)
      (by simp) (by simp [closedRelativeBasepoint])).trans (Category.comp_id _)
  have := closedRelativeFiberPointMap_isIso P
  change (Q.map (homotopyPullbackComparison (closedRelativeSquare P).flip) ≫
    inv (Q.map (closedRelativeFiberPointMap P))) ≫ Q.map (closedRelativeFiberProjection P) = _
  have hm' := congrArg Q.map hm
  rw [Q.map_comp] at hm'
  rw [← hm', Category.assoc, IsIso.inv_hom_id_assoc, ← Q.map_comp]
  exact congrArg Q.map (homotopyPullbackComparison_fst (closedRelativeSquare P).flip)

/-- 概要：元の包含と c_B の合成を指定零旗へ零化する実ホモトピー。
方針：可縮な E_P で指定点のホモトピーを作り、元の定数旗から前合成。
規約：標的は元の相対実現の関手的 Ex∞ 模型。使われ方：fiber 列の零化データ。 -/
def closedRelativeNullhomotopy {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    SSet.Homotopy
      (stdSimplex.isTerminalObj₀.from (coreSRealizationFunctor.obj (closedStableModel P)) ≫
        closedRelativeBasepoint P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (closedRelativeRealization P))
      (coreSRealizationFunctor.map (closedStableInclusion P) ≫ closedRelativeConstant P ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (closedRelativeRealization P)) := by
  let : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (closedRelativeRealization P)) := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _
  let g : closedKernelRealization P ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (closedRelativeRealization P) :=
    closedKernelRealizationPost P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app (closedRelativeRealization P)
  let H : SSet.Homotopy
      (stdSimplex.isTerminalObj₀.from (closedKernelRealization P) ≫ closedKernelZeroFlag P ≫ g)
      g := Classical.choice (specifiedPoint_map_homotopy (closedKernelZeroFlag P) g
        (closedKernelRealization_toPoint_isIso P))
  have ht : closedKernelConstant P ≫ stdSimplex.isTerminalObj₀.from (closedKernelRealization P) =
      stdSimplex.isTerminalObj₀.from (coreSRealizationFunctor.obj (closedStableModel P)) :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  let H' := HomotopyClasses.preHomotopy (closedKernelConstant P) H
  refine { h := H'.h, h₀ := ?_, h₁ := ?_, rel := ?_ }
  · have h₀ : SSet.ι₀ ≫ H'.h = closedKernelConstant P ≫
        (stdSimplex.isTerminalObj₀.from (closedKernelRealization P) ≫ closedKernelZeroFlag P ≫ g) :=
      H'.h₀
    exact h₀.trans (by
      simp only [g, closedRelativeBasepoint, ← Category.assoc, ht]
      rfl)
  · have h₁ : SSet.ι₁ ≫ H'.h = closedKernelConstant P ≫ g := H'.h₁
    exact h₁.trans (by
      simp only [g, ← Category.assoc, (closedRelativeSquare P).w]
      rfl)
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.KST.Fibration.Relative
