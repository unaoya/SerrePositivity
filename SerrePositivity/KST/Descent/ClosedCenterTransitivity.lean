module

public import SerrePositivity.KST.Descent.ThickeningDescent
public import SerrePositivity.KST.Descent.ReducedSourceDescent
public import SerrePositivity.KST.Descent.FiniteTypeUniversal
public import SerrePositivity.KST.Descent.TranslatedSections

/-!
# 実際の閉中心上の切断と点の推移性

## 概要
元の射の点のファイバーの推移性と切断を、閉中心への実際の引き戻しへ移す。

## 方針
第一射影の閉埋め込み性から点の単射性を使う。切断は引き戻しの普遍性で構成する。

## 規約
中心をアフィン表示に置き換えず、指定された引き戻しとその作用を保持する。

## 使われ方
論文 補題 3.3・定理 3.1 の真閉中心上の帰納と、始域の被約化後の軌道被覆。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {X Y Z : FiniteTypeSchemes S} {G : Type u} [Group G]
variable (f : X ⟶ Y) (i : Z ⟶ Y) [IsClosedImmersion i.hom.left]
variable (action : G →* Aut X) (over_base : ∀ g, (action g).asIso.hom ≫ f = f)

/-- 概要：閉中心への引き戻しは点のファイバーの推移性を保つ（論文 定理 3.1）。
方針：元のファイバーを結ぶ群元を選び、第一射影の同変性と点の単射性を使う。
規約：中心は任意の閉埋め込みで、被約性もアフィン性も不要。
使われ方：実際の中心上の射に対する移動切断の被覆。 -/
theorem closedBaseChangeAction_transitive_on_fibers
    (transitive : ∀ x y : X.obj.left, f.hom.left x = f.hom.left y →
      ∃ g : G, (action g).asIso.hom.hom.left x = y)
    (x y : (closedImmersionPullback f i).obj.left)
    (same_base : (closedImmersionSquare f i).f₁₃.hom.left x =
      (closedImmersionSquare f i).f₁₃.hom.left y) :
    ∃ g : G, (closedBaseChangeAction f i action over_base g).asIso.hom.hom.left x = y := by
  have first_closed : IsClosedImmersion (closedImmersionSquare f i).f₁₂.hom.left :=
    inferInstanceAs (IsClosedImmersion (pullback.fst f.hom.left i.hom.left))
  have comm (z : (closedImmersionPullback f i).obj.left) :=
    congrArg (fun k : closedImmersionPullback f i ⟶ Y ↦ k.hom.left z)
      (closedImmersionSquare f i).fac
  have equal_base : f.hom.left ((closedImmersionSquare f i).f₁₂.hom.left x) =
      f.hom.left ((closedImmersionSquare f i).f₁₂.hom.left y) :=
    (comm x).trans ((congrArg i.hom.left same_base).trans (comm y).symm)
  obtain ⟨g, hg⟩ := transitive _ _ equal_base
  refine ⟨g, (closedImmersionSquare f i).f₁₂.hom.left.isClosedEmbedding.injective ?_⟩
  have equivariant := congrArg
    (fun k : closedImmersionPullback f i ⟶ X ↦ k.hom.left x)
    (closedPullbackAction_fst f i action 1 1
      (fun g ↦ by simpa using over_base g) (fun _ ↦ by simp) g)
  exact equivariant.trans hg

/-- 概要：元の切断を閉中心への引き戻しの切断にする（論文 定理 3.1）。
方針：中心の包含と元の切断の合成、および中心の恒等射を持ち上げる。
規約：群作用はこの構成には不要。
使われ方：中心上の帰納で切断の存在を引き継ぐ。 -/
noncomputable def closedBaseChangeSection (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) :
    Z ⟶ closedImmersionPullback f i :=
  closedImmersionPullbackLift f i (i ≫ s) (𝟙 Z) (by simp [Category.assoc, hs])

/-- 概要：構成した閉中心上の射は指定された第二射影の切断（論文 定理 3.1）。
方針：引き戻しの持ち上げの第二射影の公式を使う。
規約：有限型の圏内の射の等式。
使われ方：中心上の移動切断の構成。 -/
@[reassoc (attr := simp)] theorem closedBaseChangeSection_identity
    (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) :
    closedBaseChangeSection f i s hs ≫ (closedImmersionSquare f i).f₁₃ = 𝟙 Z :=
  closedImmersionPullbackLift_snd f i (i ≫ s) (𝟙 Z) _

/-- 概要：中心上の元の切断の移動が実際の引き戻し全体を覆う（論文 定理 3.1）。
方針：閉中心上へ移した点の推移性と構成した切断を被覆判定に適用する。
規約：像の被覆を別の仮定にしない。
使われ方：中心上の軌道正方形の被覆条件。 -/
theorem closedBaseChangeSection_covering
    (transitive : ∀ x y : X.obj.left, f.hom.left x = f.hom.left y →
      ∃ g : G, (action g).asIso.hom.hom.left x = y)
    (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) :
    ⋃ t : TranslatedSectionIndex (closedBaseChangeAction f i action over_base)
      (closedBaseChangeSection f i s hs), Set.range t.val.hom.left = Set.univ :=
  translatedSection_covering (closedImmersionSquare f i).f₁₃ _
    (closedBaseChangeSection_identity f i s hs) _
    (closedBaseChangeAction_transitive_on_fibers f i action over_base transitive)

/-- 概要：被約な閉中心では始域を被約化した後の移動切断も全体を覆う（定理 3.1）。
方針：構成した切断を被約化へ持ち上げ、点の推移性を包含で移す。
規約：元の切断から構成し、被約化後の切断や被覆を追加仮定にしない。
使われ方：被約な対象に対する次元帰納に入力する中心上の軌道被覆。 -/
theorem closedBaseChange_reducedSection_covering [IsReduced Z.obj.left]
    (transitive : ∀ x y : X.obj.left, f.hom.left x = f.hom.left y →
      ∃ g : G, (action g).asIso.hom.hom.left x = y)
    (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) :
    ⋃ t : TranslatedSectionIndex
        (finiteTypeReductionAction (closedBaseChangeAction f i action over_base))
        (finiteTypeReductionLift (closedBaseChangeSection f i s hs)),
      Set.range t.val.hom.left = Set.univ := by
  refine translatedSection_covering (B := Z)
    (finiteTypeReductionInclusion (closedImmersionPullback f i) ≫
      (closedImmersionSquare f i).f₁₃)
    (finiteTypeReductionLift (X := Z) (closedBaseChangeSection f i s hs)) ?_
    (finiteTypeReductionAction (closedBaseChangeAction f i action over_base)) ?_
  · exact (finiteTypeReductionLift_comp_inclusion_assoc
      (closedBaseChangeSection f i s hs) (closedImmersionSquare f i).f₁₃).trans
        (closedBaseChangeSection_identity f i s hs)
  · exact reducedSourceAction_transitive_on_fibers _ _
      (closedBaseChangeAction_transitive_on_fibers f i action over_base transitive)

end SerrePositivity.KST.Descent
