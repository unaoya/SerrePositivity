module

public import SerrePositivity.InfinityCategories.F2.OverBousfieldKanComparisonSurjective
public import SerrePositivity.InfinityCategories.F2.BousfieldKanWeightLiftNormalization

/-!
概要：Over 圏の生成元の忘却と終点への持ち上げ直しは余極限で元に戻る。
方針：終点の構造射の余極限関係式と底の恒等成分の coend 関係式を使う。
規約：比較には filtered 性も Kan 性も不要。
使われ方：標準比較の各次数の単射性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {I : Type u} [SmallCategory I]

/-- 概要：Over 圏の元の生成元と終点へ持ち上げ直した生成元は余極限で一致する。
方針：Over の構造射を余極限で消し、底の恒等成分の射を coend で消す。
規約：係数の単体は元のものを保つ。使われ方：次数ごとの他方の逆則。 -/
lemma overBousfieldKanDegreeLeg_normalization (F : I ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) (i : I) (a : Over i) (x : (F.obj a.left).obj d)
    (σ : (nerve (Over (Opposite.op a))).obj d) :
    overBousfieldKanDegreeLeg F d a.left (x, bousfieldKanWeightForgetSimplex σ) =
      (colimit.ι (overBousfieldKanDiagram F) i).app d
        ((weightedColimitι (bousfieldKanWeight (Over i)ᵒᵖ) (Over.forget i ⋙ F) a).app d
          (x, σ)) := by
  let w := bousfieldKanWeightForgetSimplex σ
  let j := bousfieldKanWeightEndpoint w
  let b := bousfieldKanWeightBase w
  let f : j ⟶ i := (σ.obj 0).left.unop.hom
  let p := bousfieldKanWeightSimplexLift w ⋙ Over.post (Over.map f).op
  let W := bousfieldKanWeight (Over i)ᵒᵖ
  let H := Over.forget i ⋙ F
  let z := (weightedColimitι (bousfieldKanWeight (Over j)ᵒᵖ)
    (Over.forget j ⋙ F) b).app d (x, bousfieldKanWeightSimplexLift w)
  have hc := congrArg (fun t : bousfieldKanColimit (Over.forget j ⋙ F) ⟶
      colimit (overBousfieldKanDiagram F) ↦ t.app d z)
    (colimit.w (overBousfieldKanDiagram F) f)
  have hm := overBousfieldKanι_map F f b
  have hem := congrArg (fun t ↦ t.app d (x, bousfieldKanWeightSimplexLift w)) hm
  change (overBousfieldKanMap F f).app d z =
    (weightedColimitι W H ((Over.map f).obj b)).app d (x, p) at hem
  have hn := weightedColimit_condition W H (bousfieldKanWeightNormalizationBaseMap σ)
  have hen := congrArg (fun t ↦ t.app d (x, p)) hn
  change (weightedColimitι W H a).app d
      (x, bousfieldKanWeightSimplexLift w ⋙ Over.post (Over.map f).op ⋙
        Over.map (bousfieldKanWeightNormalizationBaseMap σ).op) =
    (weightedColimitι W H ((Over.map f).obj b)).app d
      ((F.map (𝟙 a.left)).app d x, p) at hen
  rw [bousfieldKanWeightSimplexLift_normalization, F.map_id] at hen
  calc
    _ = (colimit.ι (overBousfieldKanDiagram F) i).app d
        ((overBousfieldKanMap F f).app d z) := hc.symm
    _ = (colimit.ι (overBousfieldKanDiagram F) i).app d
        ((weightedColimitι W H ((Over.map f).obj b)).app d (x, p)) :=
      congrArg ((colimit.ι (overBousfieldKanDiagram F) i).app d) hem
    _ = _ := congrArg ((colimit.ι (overBousfieldKanDiagram F) i).app d) hen.symm

end SerrePositivity.InfinityCategories.F2
