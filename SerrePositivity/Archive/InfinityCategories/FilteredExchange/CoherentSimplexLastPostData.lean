module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomComparison

/-!
概要：coherent 単体の最後の対象だけを指定射で後合成する Hom データ。
方針：最後へ入る Hom を後合成し、最後から旧頂点への空 Hom を使う。
規約：最後を含まない全 Hom を保持し、局所 Kan 性を要求しない。
使われ方：Ncomp の元の合成 prism に固定射を追加する高次整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
  (s : (SimplicialNerve C) _⦋n + 1⦌) {Y : C}
  (g : s.obj ⟨ULift.up (Fin.last (n + 1))⟩ ⟶ Y)

/-- 元の最後以外の全対象を保持し、最後だけ指定した終域にする。 -/
def coherentSimplexLastPostObj (i : Fin (n + 2)) : C :=
  Fin.lastCases Y (fun i => s.obj ⟨ULift.up i.castSucc⟩) i

/-- 最後に入る Hom だけを同じ指定射で後合成する。 -/
def coherentSimplexLastPostHom (i j : Fin (n + 2)) :
    SimplicialCategory.sHom
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up j⟩ ⟶
    SimplicialCategory.sHom (coherentSimplexLastPostObj s (Y := Y) i)
      (coherentSimplexLastPostObj s (Y := Y) j) := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      simp only [coherentSimplexLastPostObj, Fin.lastCases_last]
      exact toUnit _ ≫ eId SSet Y
    | cast j =>
      simp only [coherentSimplexLastPostObj, Fin.lastCases_last, Fin.lastCases_castSucc]
      exact coherentHomEmptyMap j _
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      simp only [coherentSimplexLastPostObj, Fin.lastCases_last, Fin.lastCases_castSucc]
      exact s.map ⟨ULift.up i.castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩ ≫
        eHomWhiskerLeft SSet (s.obj ⟨ULift.up i.castSucc⟩) g
    | cast j =>
      simp only [coherentSimplexLastPostObj, Fin.lastCases_castSucc]
      exact s.map ⟨ULift.up i.castSucc⟩ ⟨ULift.up j.castSucc⟩

end SerrePositivity.InfinityCategories.F2
