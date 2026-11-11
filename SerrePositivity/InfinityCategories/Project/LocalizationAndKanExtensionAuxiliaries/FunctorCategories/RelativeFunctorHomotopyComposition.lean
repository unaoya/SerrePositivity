module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomotopyComposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.InnerFiber
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber

/-!
概要：部分図式を固定したホモトピーを、その条件を保って合成する。
方針：前合成の fiber 内で辺を合成し、実際の合成三角形を元の関手単体集合へ戻す。
規約：部分図式の包含は単射。合成後の固定条件は射の等式。
使われ方：B1 の正方形の変形を三つの境界辺を固定して合成する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：指定した部分図式を持つ関手を制限の fiber の頂点とする。
方針：前合成の零単体への作用を計算する。
規約：固定条件は厳密な等式。
使われ方：相対ホモトピーの始点・終点。 -/
def relativeExtensionVertex {A B X : SSet.{u}} (i : A ⟶ B) (a : A ⟶ X)
    (f : B ⟶ X) (hf : i ≫ f = a) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre i).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f, by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ f) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a
    rw [hf]⟩

/-- 概要：部分図式を全時間で固定したホモトピーは制限の fiber 内の辺となる。
方針：curry の制限が指定図式の恒等辺となることを計算する。
規約：元のホモトピーの辺そのものに固定条件を添える。
使われ方：相対条件を忘れずに二つの変形を合成する。 -/
def relativeFunctorEdge {A B X : SSet.{u}} (i : A ⟶ B) (a : A ⟶ X)
    {f g : B ⟶ X} (hf : i ≫ f = a) (hg : i ≫ g = a) (H : SSet.Homotopy f g)
    (hH : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A (Δ[1] : SSet.{u}) ≫ a) :
    SSet.Truncated.Edge
      (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre i).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)))
      (relativeExtensionVertex i a f hf) (relativeExtensionVertex i a g hg) where
  edge := ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).edge, by
    have hc : curry H.h ≫ (pre i).app X = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) := by
      apply uncurry_injective
      rw [uncurry_pre_app, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
      exact hH
    change ((pre i).app X).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (curry H.h)) = _
    rw [← SSet.yonedaEquiv_comp, hc]
    rfl⟩
  src_eq := by
    apply Subtype.ext
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).src_eq
  tgt_eq := by
    apply Subtype.ext
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).tgt_eq

/-- 概要：二つの相対ホモトピーは同じ部分図式を固定したまま合成できる。
方針：制限の fiber のホモトピー圏で合成し、指定二辺の合成三角形を取り出す。
規約：合成ホモトピーとその相対条件・実際の三角形を同時に得る。
使われ方：B1 の二段階の正方形の変形の合成。 -/
lemma exists_relativeFunctorHomotopyComposite {A B X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) [Mono i] (a : A ⟶ X) {f g h : B ⟶ X}
    (hf : i ≫ f = a) (hg : i ≫ g = a) (hh : i ≫ h = a)
    (l : SSet.Homotopy f g) (r : SSet.Homotopy g h)
    (hl : (i ▷ (Δ[1] : SSet.{u})) ≫ l.h = fst A (Δ[1] : SSet.{u}) ≫ a)
    (hr : (i ▷ (Δ[1] : SSet.{u})) ≫ r.h = fst A (Δ[1] : SSet.{u}) ≫ a) :
    ∃ d : SSet.Homotopy f h,
      (i ▷ (Δ[1] : SSet.{u})) ≫ d.h = fst A (Δ[1] : SSet.{u}) ≫ a ∧
        Nonempty {T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d //
          T.diagram ≫ (pre i).app X = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)} := by
  let p := (pre i).app X
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a
  let e₀ := relativeFunctorEdge i a hf hg l hl
  let e₁ := relativeFunctorEdge i a hg hh r hr
  obtain ⟨k, hk⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _ _
    (SSet.Truncated.HomotopyCategory.homMk e₀ ≫ SSet.Truncated.HomotopyCategory.homMk e₁)
  obtain ⟨t⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac hk.symm
  let k' := k.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b))
  let t' := t.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b))
  let d := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge k'
  have hd : (i ▷ (Δ[1] : SSet.{u})) ≫ d.h = fst A (Δ[1] : SSet.{u}) ≫ a := by
    have hp : (SSet.yonedaEquiv.symm k'.edge) ≫ p = SSet.const b := by
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
      change p.app (Opposite.op ⦋1⦌) k.edge.val = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 1
      exact k.edge.property
    change (i ▷ (Δ[1] : SSet.{u})) ≫ uncurry (SSet.yonedaEquiv.symm k'.edge) = _
    rw [← uncurry_pre_app]
    change uncurry (SSet.yonedaEquiv.symm k'.edge ≫ p) = _
    rw [hp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
    rfl
  refine ⟨d, hd, ⟨⟨⟨SSet.yonedaEquiv.symm t'.simplex, ?_, ?_, ?_⟩, ?_⟩⟩⟩
  · apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    have ht := t'.d₀
    change ((ihom B).obj X).δ 0 t'.simplex = SSet.yonedaEquiv (curry r.h) at ht
    exact ht
  · apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    change _ = SSet.yonedaEquiv (curry (uncurry (SSet.yonedaEquiv.symm k'.edge)))
    rw [curry_uncurry, Equiv.apply_symm_apply]
    exact t'.d₁
  · apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    have ht := t'.d₂
    change ((ihom B).obj X).δ 2 t'.simplex = SSet.yonedaEquiv (curry l.h) at ht
    exact ht
  · apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    change p.app (Opposite.op ⦋2⦌) t.simplex.val = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant b 2
    exact t.simplex.property

section
variable {A B X : SSet.{u}} [Quasicategory X]
variable (i : A ⟶ B) [Mono i] (a : A ⟶ X) {f g h : B ⟶ X}
variable (hf : i ≫ f = a) (hg : i ≫ g = a) (hh : i ≫ h = a)
variable (l : SSet.Homotopy f g) (r : SSet.Homotopy g h)
variable (hl : (i ▷ (Δ[1] : SSet.{u})) ≫ l.h = fst A (Δ[1] : SSet.{u}) ≫ a)
variable (hr : (i ▷ (Δ[1] : SSet.{u})) ≫ r.h = fst A (Δ[1] : SSet.{u}) ≫ a)

/-- 概要：部分図式を固定する合成ホモトピーを選ぶ。
方針：fiber 内の合成の存在証明から取り出す。
規約：入力の二経路と固定条件を指定する。
使われ方：三辺固定の正方形の二段階の変形の合成。 -/
noncomputable def relativeFunctorHomotopyComposite : SSet.Homotopy f h :=
  (exists_relativeFunctorHomotopyComposite i a hf hg hh l r hl hr).choose

/-- 概要：選んだ合成も指定部分図式を全時間で固定する。
方針：相対合成の選択の仕様を読む。
規約：時間方向の射の等式。
使われ方：合成後の三辺の固定条件。 -/
lemma relativeFunctorHomotopyComposite_restriction :
    (i ▷ (Δ[1] : SSet.{u})) ≫ (relativeFunctorHomotopyComposite i a hf hg hh l r hl hr).h =
      fst A (Δ[1] : SSet.{u}) ≫ a :=
  (exists_relativeFunctorHomotopyComposite i a hf hg hh l r hl hr).choose_spec.1

/-- 概要：相対合成は元の指定二経路を辺とする実際の三角形を持つ。
方針：同じ fiber 内の合成の存在証明から二単体を取り出す。
規約：二経路の代表を変更しない。
使われ方：三辺固定の合成と元の二段階の変形の整合性。 -/
noncomputable def relativeFunctorHomotopyCompositeTriangle :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r (relativeFunctorHomotopyComposite i a hf hg hh l r hl hr) :=
  (exists_relativeFunctorHomotopyComposite i a hf hg hh l r hl hr).choose_spec.2.some.val

/-- 概要：相対合成の二単体そのものも部分図式の上で定値となる。
方針：fiber 内で得た二単体の固定条件を同じ選択から取り出す。
規約：三辺だけの固定より強い、二単体全体の固定条件。
使われ方：境界の path の合成を二次の coherence まで保って比較する。 -/
lemma relativeFunctorHomotopyCompositeTriangle_restriction :
    (relativeFunctorHomotopyCompositeTriangle i a hf hg hh l r hl hr).diagram ≫ (pre i).app X =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a) :=
  (exists_relativeFunctorHomotopyComposite i a hf hg hh l r hl hr).choose_spec.2.some.property

end

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
