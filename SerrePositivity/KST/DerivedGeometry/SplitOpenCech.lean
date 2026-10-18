module

public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Cech
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.CategoryTheory.Limits.Lattice

/-!
概要：全体を含む開被覆の Čech 対象の追加退化を構成する。
方針：全体に等しい被覆要素の添字を先頭へ挿入する。
規約：形式的余積と実際の開集合の有限交叉を使う。
使われ方：TT §3、Toën §3.2 の基本開局所化後の Čech 収縮。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable {X : Type u} [TopologicalSpace X] {ι : Type v} (U : ι → Opens X)

/--
概要：開集合族の Čech 対象を全体の開集合へ増大する。
方針：各交叉から全体への包含を形式的余積上で束ねる。
規約：Čech 対象は Mathlib の有限積による構成そのもの。
使われ方：TT §3、Toën §3.2 の Čech 複体の増大。
-/
def openCechAugmented : SimplicialObject.Augmented (FormalCoproduct.{v} (Opens X)) where
  left := (FormalCoproduct.mk ι U).cech
  right := (FormalCoproduct.incl (Opens X)).obj ⊤
  hom :=
    { app := fun _ => ⟨fun _ => PUnit.unit, fun _ => homOfLE le_top⟩
      naturality := by
        intros
        exact FormalCoproduct.hom_ext rfl (fun _ => Subsingleton.elim _ _) }

/--
概要：全体に等しい被覆要素への先頭挿入は Čech 対象の追加退化を与える。
方針：添字の先頭挿入と有限積の射影で追加退化の各恒等式を検証する。
規約：収縮の存在を仮定として渡さない。
使われ方：TT §3、Toën §3.2 のアフィン Čech 計算。
-/
def splitOpenCechExtraDegeneracy (j : ι) (hj : U j = ⊤) :
    SimplicialObject.Augmented.ExtraDegeneracy (openCechAugmented U) where
  s' :=
    { f := fun _ _ => j
      φ := fun _ => Pi.lift (fun _ => homOfLE (by change (⊤ : Opens X) ≤ U j; rw [hj])) }
  s n :=
    { f := fun t => Fin.cons j t
      φ t := Pi.lift (fun a => by
        refine Fin.cases ?_ (fun k => ?_) a
        · exact homOfLE (by change _ ≤ U j; rw [hj]; exact le_top)
        · exact Pi.π _ k) }
  s'_comp_ε := by
    exact FormalCoproduct.hom_ext rfl (fun _ => Subsingleton.elim _ _)
  s₀_comp_δ₁ := by
    refine FormalCoproduct.hom_ext ?_ (fun _ => Subsingleton.elim _ _)
    funext t a
    fin_cases a
    rfl
  s_comp_δ₀ n := by
    refine FormalCoproduct.hom_ext ?_ (fun _ => Subsingleton.elim _ _)
    funext t a
    rfl
  s_comp_δ n i := by
    refine FormalCoproduct.hom_ext ?_ (fun _ => Subsingleton.elim _ _)
    funext t a
    refine Fin.cases ?_ (fun k => ?_) a
    · rfl
    · simp [openCechAugmented, SimplicialObject.δ, FormalCoproduct.cech, FormalCoproduct.mapPower, SimplexCategory.δ, SimplexCategory.σ]
  s_comp_σ n i := by
    refine FormalCoproduct.hom_ext ?_ (fun _ => Subsingleton.elim _ _)
    funext t a
    refine Fin.cases ?_ (fun k => ?_) a
    · rfl
    · simp [openCechAugmented, SimplicialObject.σ, FormalCoproduct.cech, FormalCoproduct.mapPower, SimplexCategory.δ, SimplexCategory.σ]

end SerrePositivity.KST.DerivedGeometry
