module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberwiseHomFiberNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ConeFamily

/-!
概要：全空間上の図式が定める fiber ごとの族と、各 fiber への通常の制限を同定する。
方針：頂点で定値なパラメータへ制限し、fiber の関手空間の普遍性を計算する。
規約：底・全空間・標的の充填性は不要。
使われ方：点ごとの余極限を相対 join の族の存在へ渡す。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：全空間上の図式の各 fiber への制限をまとめた族。
方針：恒等射に沿う逆像の第二射影から元の図式を読み、curry する。
規約：底は C の恒等射。
使われ方：一般の図式から普遍余錐の族への入力。 -/
def kanGlobalDiagramFamily {K C D : SSet.{u}} (p : K ⟶ C) (F : K ⟶ D) :
    C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHom p D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry p (𝟙 C) (pullback.snd (𝟙 C) p ≫ F)

/-- 概要：全空間の図式の族は恒等射の上にある。
方針：curry の射影の公式。
規約：射の厳密な等式。
使われ方：各頂点での fiber への持ち上げ。 -/
lemma kanGlobalDiagramFamily_projection {K C D : SSet.{u}} (p : K ⟶ C) (F : K ⟶ D) :
    kanGlobalDiagramFamily p F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p D = 𝟙 C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry_projection p (𝟙 C) _

/-- 概要：全空間の図式の族を頂点へ制限すると、その fiber への図式の制限になる。
方針：fiber の Hom 比較と定値逆像の射影を計算し、curry の自然性と照合する。
規約：定値な零単体をパラメータとする等式。
使われ方：各 fiber の余極限余錐を族の頂点へ対応させる。 -/
lemma kanGlobalDiagramFamily_fiber {K C D : SSet.{u}} (p : K ⟶ C) (F : K ⟶ D)
    (c : C _⦋0⦌) :
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c ≫ F)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseHomFiberIso p c D).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p D) c =
        (SSet.const c : Δ[0] ⟶ C) ≫ kanGlobalDiagramFamily p F := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseHomFiberIso_hom_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseHomFiberHomEquiv_apply_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uncurry_yoneda_functorVertex]
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.constantPullbackIso p c (Δ[0] : SSet.{u})).hom ≫
      fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c) Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c ≫ F) =
        pullback.snd (SSet.const c : Δ[0] ⟶ C) p ≫ F := by
    exact (congrArg (fun z ↦ z ≫ F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.constantPullbackIso_hom_fst_ι p c (Δ[0] : SSet.{u})))
  rw [he]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorCurry_precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p)
    (⟨𝟙 C, pullback.snd (𝟙 C) p ≫ F⟩ :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseFunctorSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p) D C) (SSet.const c : Δ[0] ⟶ C)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry p (SSet.const c : Δ[0] ⟶ C)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map
      (Over.homMk (SSet.const c : Δ[0] ⟶ C) rfl :
        Over.mk (SSet.const c : Δ[0] ⟶ C) ⟶ Over.mk (𝟙 C)) ≫
          pullback.snd (𝟙 C) p ≫ F) = _ at h
  rw [← Category.assoc] at h
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying_map_snd] at h
  exact h

/-- 概要：fiber の通常の制限の関手頂点は大域図式の族の同じ頂点に対応する。
方針：定値零単体上の比較に Yoneda 対応を適用する。
規約：fiber の頂点の値を全空間へ戻した等式。
使われ方：普遍余錐の頂点と元の図式の族の頂点を照合する。 -/
lemma kanGlobalDiagramFamily_fiber_vertex {K C D : SSet.{u}} (p : K ⟶ C) (F : K ⟶ D)
    (c : C _⦋0⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseHomFiberIso p c D).hom.app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p c ≫ F))).val =
        (kanGlobalDiagramFamily p F).app (Opposite.op ⦋0⦌) c := by
  have h := congrArg SSet.yonedaEquiv (kanGlobalDiagramFamily_fiber p F c)
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, SSet.yonedaEquiv_const] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
