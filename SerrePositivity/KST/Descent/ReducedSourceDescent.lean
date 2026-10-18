module

public import SerrePositivity.KST.Descent.ReductionDescent

/-!
# 基底を固定した始域の被約化

## 概要
基底を固定し、射の始域だけを被約化しても全次数の降下が同値であることを証明する。

## 方針
被約化の包含の同変性と冪零不変性を、基底の恒等射との比較正方形に適用する。

## 規約
Noether 性は始域だけに要求する。基底の被約性はこの比較には不要。

## 使われ方
論文 補題 3.3・定理 3.1 の真閉中心 Z 上で、非被約な V ×_B Z を被約化する。
-/

@[expose] public section

universe u w t

open CategoryTheory AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {X Y : FiniteTypeSchemes S} {G : Type*} [Group G]

/-- 概要：始域だけを被約化した射も基底上の作用を保つ（論文 §3）。
方針：包含の同変性と元の射の不変性を合成する。
規約：終域 Y は被約化しない。
使われ方：中心の被約化上の PiDescent の指定可換式。 -/
theorem reducedSourceAction_over_base (f : X ⟶ Y) (action : G →* Aut X)
    (over_base : ∀ g, (action g).asIso.hom ≫ f = f) (g : G) :
    (finiteTypeReductionAction action g).asIso.hom ≫
      (finiteTypeReductionInclusion X ≫ f) = finiteTypeReductionInclusion X ≫ f := by
  rw [← Category.assoc, finiteTypeReductionAction_comp_inclusion, Category.assoc, over_base]

/-- 概要：基底を固定した始域の被約化は点のファイバーの推移性を保つ（定理 3.1）。
方針：包含の同変性と点の単射性を使い、元のファイバーを結ぶ群元を被約化へ移す。
規約：これは基礎点のファイバーの推移性であり、幾何的推移性の定義との同一視ではない。
使われ方：アフィン基底変更後の中心の被約化に対する切断の像の被覆。 -/
theorem reducedSourceAction_transitive_on_fibers (f : X ⟶ Y) (action : G →* Aut X)
    (transitive : ∀ x y : X.obj.left, f.hom.left x = f.hom.left y →
      ∃ g : G, (action g).asIso.hom.hom.left x = y)
    (x y : (finiteTypeReduction X).obj.left)
    (same_base : (finiteTypeReductionInclusion X ≫ f).hom.left x =
      (finiteTypeReductionInclusion X ≫ f).hom.left y) :
    ∃ g : G, (finiteTypeReductionAction action g).asIso.hom.hom.left x = y := by
  obtain ⟨g, hg⟩ := transitive
    ((finiteTypeReductionInclusion X).hom.left x)
    ((finiteTypeReductionInclusion X).hom.left y) same_base
  refine ⟨g, (finiteTypeReductionInclusion X).hom.left.isClosedEmbedding.injective ?_⟩
  have equivariant := congrArg
    (fun k : finiteTypeReduction X ⟶ X ↦ k.hom.left x)
    (finiteTypeReductionAction_comp_inclusion action g)
  exact equivariant.trans hg

/-- 概要：始域だけの被約化の前後で全次数降下は同値（論文 補題 3.3）。
方針：基底の恒等射と被約化の包含による正方形に冪零不変性を適用する。
規約：始域の Noether 性だけを使い、任意の係数と整数次数を保持する。
使われ方：真閉中心上の帰納仮定を実際の非被約な中心の射へ移す。 -/
theorem Nilinvariant.piDescent_iff_reducedSource {Coefficient : Type w}
    (L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient)
    [Nilinvariant S L] [IsNoetherian X.obj.left]
    (f : X ⟶ Y) (action : G →* Aut X)
    (over_base : ∀ g, (action g).asIso.hom ≫ f = f) :
    L.PiDescent f action over_base ↔
      L.PiDescent (finiteTypeReductionInclusion X ≫ f) (finiteTypeReductionAction action)
        (reducedSourceAction_over_base f action over_base) := by
  apply L.piDescent_iff_of_bijective_square f (finiteTypeReductionInclusion X ≫ f)
    (finiteTypeReductionInclusion X) (𝟙 Y) (by simp)
    action (finiteTypeReductionAction action) over_base
    (reducedSourceAction_over_base f action over_base)
    (finiteTypeReductionAction_comp_inclusion action)
  · exact Nilinvariant.noetherianReduction_pullback_bijective L X
  · intro H n
    rw [L.pullback_id]
    exact Function.bijective_id

end SerrePositivity.KST.Descent
