module

public import SerrePositivity.InfinityCategories.F1B.IntervalFamilySquare
public import SerrePositivity.InfinityCategories.F1B.ConstantFunctor
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.Core.HomotopyBoundaryExtension

/-!
概要：写像空間の族のホモトピーを、矢印を動かす可逆 path の図式へ移す。
方針：関手正方形の二つの区間を交換して curry し、固定端点での退化性を使う。
規約：始域・標的の quasicategory 性は不要。
使われ方：導来 fiber のホモトピーを三角形の対角辺の path に組み込む。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：正方形を交換して curry した図式の頂点は対応する縦辺の関手頂点。
方針：零単体への添字写像の一意性と内部 Hom の評価を計算する。
規約：第一座標を矢印、第二座標を時間とする。
使われ方：固定端点の縦辺の可逆性を確認する。 -/
lemma transposeSquare_vertex {Z : SSet.{u}}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Z) (i : Fin 2) :
    (curry ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ Q)).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm i) = functorVertex (prismEndpoint i Δ[1] ≫ Q) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  have hα : α = (SimplexCategory.const d.unop ⦋0⦌ 0).op := Subsingleton.elim _ _
  subst α
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：写像空間のホモトピーが表す矢印の可逆 path の図式。
方針：関手正方形を交換して curry し、二端点での縦辺が定値であることを使う。
規約：可逆なのは矢印を動かす方向で、矢印自体の可逆性は仮定しない。
使われ方：三角形の対角辺に与える path。 -/
noncomputable def intervalFamilyPath {A X : SSet.{u}} {x y : X _⦋0⦌}
    {f g : A ⟶ intervalMappingSpace x y} (H : SSet.Homotopy f g) :
    (Δ[1] : SSet.{u}) ⟶ equivalencePath ((ihom A).obj X) :=
  fullSubcomplexLift IsEquivalencePathVertex
    (curry ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ intervalFamilySquare H)) (fun z ↦ by
      obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective z
      rw [transposeSquare_vertex]
      fin_cases i
      · change IsEquivalencePathVertex (functorVertex
          (prismEndpoint 0 Δ[1] ≫ intervalFamilySquare H))
        rw [intervalFamilySquare_source]
        exact isEquivalencePathVertex_const _
      · change IsEquivalencePathVertex (functorVertex
          (prismEndpoint 1 Δ[1] ≫ intervalFamilySquare H))
        rw [intervalFamilySquare_target]
        exact isEquivalencePathVertex_const _)

/-- 概要：可逆 path の図式を包含すると交換した関手正方形の curry。
方針：全部分複体への持ち上げの公式。
規約：実際の図式を保持する。
使われ方：端点と始点・終点の計算。 -/
lemma intervalFamilyPath_ι {A X : SSet.{u}} {x y : X _⦋0⦌}
    {f g : A ⟶ intervalMappingSpace x y} (H : SSet.Homotopy f g) :
    intervalFamilyPath H ≫ equivalencePathι _ =
      curry ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ intervalFamilySquare H) :=
  fullSubcomplexLift_ι _ _ _

/-- 概要：可逆 path の始点は最初の族の矢印の表示。
方針：curry の端点評価と正方形の下辺を計算する。
規約：厳密な等式。
使われ方：基準三角形の対角辺との一致。 -/
lemma intervalFamilyPath_start {A X : SSet.{u}} {x y : X _⦋0⦌}
    {f g : A ⟶ intervalMappingSpace x y} (H : SSet.Homotopy f g) :
    intervalFamilyPath H ≫ equivalencePathEndpoint _ 0 = curry (intervalFamilyHomotopy f).h := by
  rw [equivalencePathEndpoint, ← Category.assoc, intervalFamilyPath_ι,
    curry_evaluateFunctorAt_interval, ← Category.assoc, prismEndpoint_zero_braiding]
  exact intervalFamilySquare_zero H

/-- 概要：可逆 path の終点は最後の族の矢印の表示。
方針：curry の端点評価と正方形の上辺を計算する。
規約：厳密な等式。
使われ方：運んだ三角形の新しい対角辺。 -/
lemma intervalFamilyPath_end {A X : SSet.{u}} {x y : X _⦋0⦌}
    {f g : A ⟶ intervalMappingSpace x y} (H : SSet.Homotopy f g) :
    intervalFamilyPath H ≫ equivalencePathEndpoint _ 1 = curry (intervalFamilyHomotopy g).h := by
  rw [equivalencePathEndpoint, ← Category.assoc, intervalFamilyPath_ι,
    curry_evaluateFunctorAt_interval, ← Category.assoc, prismEndpoint_one_braiding]
  exact intervalFamilySquare_one H

/-- 概要：矢印の始点での縦 path は定値 path。
方針：包含で検査し、交換した正方形の頂点を計算する。
規約：始点 x の定値関手は動かさない。
使われ方：三角形の境界の頂点での貼り合わせ。 -/
lemma intervalFamilyPath_source {A X : SSet.{u}} {x y : X _⦋0⦌}
    {f g : A ⟶ intervalMappingSpace x y} (H : SSet.Homotopy f g) :
    stdSimplex.δ (1 : Fin 2) ≫ intervalFamilyPath H =
      SSet.const (functorVertex (SSet.const x : A ⟶ X)) ≫ equivalencePathRefl _ := by
  have : Mono (equivalencePathι ((ihom A).obj X)) := by
    dsimp [equivalencePathι]
    infer_instance
  apply (cancel_mono (equivalencePathι ((ihom A).obj X))).mp
  rw [Category.assoc, intervalFamilyPath_ι, Category.assoc]
  rw [show equivalencePathRefl ((ihom A).obj X) ≫ equivalencePathι _ =
    curry (snd (Δ[1] : SSet.{u}) ((ihom A).obj X)) from fullSubcomplexLift_ι _ _ _]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp]
  rw [show SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2)) =
    stdSimplex.obj₀Equiv.symm 0 by decide]
  rw [show SSet.yonedaEquiv (SSet.const (functorVertex (SSet.const x : A ⟶ X)) :
    (Δ[0] : SSet.{u}) ⟶ (ihom A).obj X) = functorVertex (SSet.const x : A ⟶ X)
      from SSet.yonedaEquiv_const _]
  change (curry ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ intervalFamilySquare H)).app
    (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0) =
      (constantFunctorMap Δ[1] ((ihom A).obj X)).app (Opposite.op ⦋0⦌)
        (functorVertex (SSet.const x : A ⟶ X))
  rw [transposeSquare_vertex, intervalFamilySquare_source, constantFunctorMap_vertex]

/-- 概要：矢印の終点での縦 path は定値 path。
方針：包含で検査し、交換した正方形の頂点を計算する。
規約：終点 y の定値関手は動かさない。
使われ方：三角形の境界の頂点での貼り合わせ。 -/
lemma intervalFamilyPath_target {A X : SSet.{u}} {x y : X _⦋0⦌}
    {f g : A ⟶ intervalMappingSpace x y} (H : SSet.Homotopy f g) :
    stdSimplex.δ (0 : Fin 2) ≫ intervalFamilyPath H =
      SSet.const (functorVertex (SSet.const y : A ⟶ X)) ≫ equivalencePathRefl _ := by
  have : Mono (equivalencePathι ((ihom A).obj X)) := by
    dsimp [equivalencePathι]
    infer_instance
  apply (cancel_mono (equivalencePathι ((ihom A).obj X))).mp
  rw [Category.assoc, intervalFamilyPath_ι, Category.assoc]
  rw [show equivalencePathRefl ((ihom A).obj X) ≫ equivalencePathι _ =
    curry (snd (Δ[1] : SSet.{u}) ((ihom A).obj X)) from fullSubcomplexLift_ι _ _ _]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp]
  rw [show SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2)) =
    stdSimplex.obj₀Equiv.symm 1 by decide]
  rw [show SSet.yonedaEquiv (SSet.const (functorVertex (SSet.const y : A ⟶ X)) :
    (Δ[0] : SSet.{u}) ⟶ (ihom A).obj X) = functorVertex (SSet.const y : A ⟶ X)
      from SSet.yonedaEquiv_const _]
  change (curry ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ intervalFamilySquare H)).app
    (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1) =
      (constantFunctorMap Δ[1] ((ihom A).obj X)).app (Opposite.op ⦋0⦌)
        (functorVertex (SSet.const y : A ⟶ X))
  rw [transposeSquare_vertex, intervalFamilySquare_target, constantFunctorMap_vertex]

end SerrePositivity.InfinityCategories
