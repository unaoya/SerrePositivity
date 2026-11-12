module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.MooreUniverse
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyGroups

/-! # 単体的加群の境界零単体

概要：零に基点を持つ境界定数単体は、全ての面が零の元と同じである。
方針：Yoneda の全単射と境界の面による生成を使う。
規約：正次数 n+1。使われ方：K-L9 のホモトピー群と Moore ホモロジーの比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory AlgebraicTopology
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] (W : SimplicialObject (ModuleCat.{v} S))

/-- 概要：単体的加群の忘却単体集合。
方針：各次数で加群構造を忘れる。規約：同じ台集合。使われ方：ホモトピー群の入力。 -/
abbrev moduleUnderlyingSSet : SSet.{v} := W ⋙ forget (ModuleCat.{v} S)

/-- 概要：忘却された単体の値を元の加群の元として取る。
方針：台集合の恒等写像を型として明示する。
規約：値は変えない。使われ方：線形演算の型クラスの指定。 -/
def moduleSimplexValue (n : ℕ) (t : (moduleUnderlyingSSet W) _⦋n⦌) :
    W.obj (Opposite.op ⦋n⦌) := t

/-- 概要：全ての面が零の正次数の単体の部分加群。
方針：全ての面写像の核を交わす。
規約：次数 n+1。使われ方：Moore の cycles の具体的表示。 -/
def sphericalModule (n : ℕ) : Submodule S (W.obj (Opposite.op ⦋n + 1⦌)) :=
  ⨅ j : Fin (n + 2), LinearMap.ker (W.δ j).hom

/-- 概要：零頂点への定値射の全ての成分は零。
方針：単体的加群の射は零を保つ。
規約：任意の始域。使われ方：境界定数条件の線形表示。 -/
lemma module_const_zero_apply {X : SSet.{v}} (n : SimplexCategoryᵒᵖ) (s : X.obj n) :
    (SSet.const (X := X) (0 : (moduleUnderlyingSSet W) _⦋0⦌)).app n s = 0 := by
  change (W.map (n.unop.const _ 0).op) 0 = 0
  exact map_zero _

/-- 概要：零への定値単体は Yoneda 座標で零となる。
方針：Yoneda の評価で定値射を計算する。
規約：任意の次数。使われ方：面の零性。 -/
lemma module_yoneda_const_zero (n : ℕ) :
    SSet.yonedaEquiv (SSet.const (X := Δ[n]) (0 : (moduleUnderlyingSSet W) _⦋0⦌)) =
      (0 : W.obj (Opposite.op ⦋n⦌)) := by
  exact module_const_zero_apply W (X := Δ[n]) (Opposite.op ⦋n⦌) (ULift.up (𝟙 ⦋n⦌))

/-- 概要：境界が零の単体の各面は零。
方針：境界条件を面に制限して Yoneda 座標で評価する。
規約：正次数。使われ方：具体的 cycles への写像。 -/
lemma pointedModule_face_zero {n : ℕ}
    (f : (moduleUnderlyingSSet W).PtSimplex (n + 1) 0) (j : Fin (n + 2)) :
    W.δ j (SSet.yonedaEquiv f.map) = 0 := by
  have h := congrArg SSet.yonedaEquiv (f.δ_map j)
  rw [SSet.stdSimplex.yonedaEquiv_δ_comp, module_yoneda_const_zero] at h
  exact h

/-- 概要：境界零の単体と全ての面が零の元は全単射である。
方針：Yoneda の全単射を境界条件に制限する。
規約：正次数 n+1。使われ方：π の代表を Moore cycles へ送る。 -/
def pointedModuleSimplexEquiv (n : ℕ) :
    (moduleUnderlyingSSet W).PtSimplex (n + 1) 0 ≃ sphericalModule W n where
  toFun f := ⟨SSet.yonedaEquiv f.map,
    (Submodule.mem_iInf _).2 (fun j => pointedModule_face_zero W f j)⟩
  invFun z :=
    { map := SSet.yonedaEquiv.symm z.val
      comm := by
        apply SSet.boundary.hom_ext
        intro j
        simp only [← Category.assoc, SSet.boundary.ι_ι, SSet.comp_const, SSet.const_comp]
        apply SSet.yonedaEquiv.injective
        rw [SSet.stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
        change W.δ j z.val = SSet.yonedaEquiv
          (SSet.const (X := Δ[n]) (0 : (moduleUnderlyingSSet W) _⦋0⦌))
        rw [module_yoneda_const_zero]
        exact (Submodule.mem_iInf _).1 z.property j }
  left_inv f := by
    apply SSet.RelativeMorphism.ext
    exact Equiv.symm_apply_apply SSet.yonedaEquiv f.map
  right_inv z := Subtype.ext (Equiv.apply_symm_apply _ _)

/-- 概要：球面座標から作った境界零単体の Yoneda 座標は元の座標である。
方針：Yoneda の両逆則を使う。
規約：元を変えない。使われ方：積の充填の線形計算。 -/
lemma pointedModuleSimplexEquiv_symm_value (n : ℕ) (z : sphericalModule W n) :
    SSet.yonedaEquiv (((pointedModuleSimplexEquiv W n).symm z).map) = z.val :=
by
  change SSet.yonedaEquiv
    ((SSet.yonedaEquiv (X := moduleUnderlyingSSet W) (n := ⦋n + 1⦌)).symm z.val) = z.val
  exact Equiv.apply_symm_apply _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
