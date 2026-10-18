module

public import SerrePositivity.KST.Descent.ClosedCoverDescent
public import SerrePositivity.KST.Descent.ClosedCenterTransitivity
public import SerrePositivity.KST.Descent.FiberTransitivityNaturality

/-!
# 閉和の交わりの指定射に対する帰納入力

## 概要
閉和の比較立方体の交わりの射へ、元の切断と点のファイバーの推移性を移す。

## 方針
二つの閉部分上の切断を交わりへ持ち上げる。推移性は同変な第一射影の単射性で移す。

## 規約
比較立方体の指定射そのものを使い、別の同型なモデルに変更しない。

## 使われ方
論文 補題 3.3・定理 3.1 の閉和の交わりに対する低次元の帰納。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} {B V Y Z : FiniteTypeSchemes S}
variable (f : V ⟶ B) (i : Y ⟶ B) (j : Z ⟶ B)
variable [IsClosedImmersion i.hom.left] [IsClosedImmersion j.hom.left]

/-- 概要：二つの閉部分上の切断は交わりへの持ち上げの条件を満たす（論文 補題 3.3）。
方針：第一射影の公式と元の交わりの可換式を合成する。
規約：指定された元の切断 s から両側を構成する。
使われ方：交わりの比較射の切断の構成。 -/
theorem closedCoverIntersectionSection_fac (s : B ⟶ V) (hs : s ≫ f = 𝟙 B) :
    ((closedImmersionSquare i j).f₁₂ ≫ closedBaseChangeSection f i s hs) ≫
        (closedImmersionSquare f i).f₁₂ =
      ((closedImmersionSquare i j).f₁₃ ≫ closedBaseChangeSection f j s hs) ≫
        (closedImmersionSquare f j).f₁₂ := by
  have left : ((closedImmersionSquare i j).f₁₂ ≫ closedBaseChangeSection f i s hs) ≫
      (closedImmersionSquare f i).f₁₂ = ((closedImmersionSquare i j).f₁₂ ≫ i) ≫ s :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k ↦ (closedImmersionSquare i j).f₁₂ ≫ k)
        (closedBaseChangeSection_first f i s hs)).trans (Category.assoc _ _ _).symm)
  have right : ((closedImmersionSquare i j).f₁₃ ≫ closedBaseChangeSection f j s hs) ≫
      (closedImmersionSquare f j).f₁₂ = ((closedImmersionSquare i j).f₁₃ ≫ j) ≫ s :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k ↦ (closedImmersionSquare i j).f₁₃ ≫ k)
        (closedBaseChangeSection_first f j s hs)).trans (Category.assoc _ _ _).symm)
  exact left.trans ((congrArg (fun k ↦ k ≫ s) (closedImmersionSquare i j).fac).trans right.symm)

/-- 概要：元の切断から交わりの比較射への切断候補を構成（論文 補題 3.3）。
方針：引き戻した交わりの普遍性を使う。
規約：元と変更後の実際の交わりの間の射。
使われ方：交わり上の局所降下に必要な切断の存在。 -/
noncomputable def closedCoverIntersectionSection (s : B ⟶ V) (hs : s ≫ f = 𝟙 B) :
    (closedImmersionSquare i j).X₁ ⟶ (closedCoverPullbackSquare f i j).X₁ :=
  (closedCoverPullbackSquare_isPullback f i j).lift
    ((closedImmersionSquare i j).f₁₂ ≫ closedBaseChangeSection f i s hs)
    ((closedImmersionSquare i j).f₁₃ ≫ closedBaseChangeSection f j s hs)
    (closedCoverIntersectionSection_fac f i j s hs)

/-- 概要：構成した交わりの射は指定比較の切断（論文 補題 3.3）。
方針：比較先の二つの射影で検査し、両側の切断の恒等式を使う。
規約：スキームの点だけでなく、有限型の圏内の射の等式を結論する。
使われ方：交わりの射を被約化しても切断を帰納へ渡す。 -/
theorem closedCoverIntersectionSection_identity (s : B ⟶ V) (hs : s ≫ f = 𝟙 B) :
    closedCoverIntersectionSection f i j s hs ≫ (closedCoverPullbackCube f i j).τ₁ =
      𝟙 (closedImmersionSquare i j).X₁ := by
  have first : closedCoverIntersectionSection f i j s hs ≫ (closedCoverPullbackSquare f i j).f₁₂ =
      (closedImmersionSquare i j).f₁₂ ≫ closedBaseChangeSection f i s hs :=
    (closedCoverPullbackSquare_isPullback f i j).lift_fst _ _ _
  have second : closedCoverIntersectionSection f i j s hs ≫ (closedCoverPullbackSquare f i j).f₁₃ =
      (closedImmersionSquare i j).f₁₃ ≫ closedBaseChangeSection f j s hs :=
    (closedCoverPullbackSquare_isPullback f i j).lift_snd _ _ _
  apply (closedImmersionSquare_isPullback i j).hom_ext
  · exact ((Category.assoc _ _ _).trans
      ((congrArg (fun k ↦ closedCoverIntersectionSection f i j s hs ≫ k)
        (closedCoverPullbackCube f i j).comm₁₂.symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k ↦ k ≫ (closedImmersionSquare f i).f₁₃) first).trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun k ↦ (closedImmersionSquare i j).f₁₂ ≫ k)
                (closedBaseChangeSection_identity f i s hs)).trans (Category.comp_id _))))))).trans
                  (Category.id_comp _).symm
  · exact ((Category.assoc _ _ _).trans
      ((congrArg (fun k ↦ closedCoverIntersectionSection f i j s hs ≫ k)
        (closedCoverPullbackCube f i j).comm₁₃.symm).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun k ↦ k ≫ (closedImmersionSquare f j).f₁₃) second).trans
            ((Category.assoc _ _ _).trans
              ((congrArg (fun k ↦ (closedImmersionSquare i j).f₁₃ ≫ k)
                (closedBaseChangeSection_identity f j s hs)).trans (Category.comp_id _))))))).trans
                  (Category.id_comp _).symm

/-- 概要：閉和の交わりの指定比較は点のファイバーの推移性を保つ（論文 定理 3.1）。
方針：左側の閉部分上での推移性と第一射影の同変性・単射性を使う。
規約：始域や交わりの被約性は要求しない。
使われ方：低次元の交わり上の局所降下の幾何的入力。 -/
theorem closedCoverIntersection_transitive_on_fibers {G : Type u} [Group G]
    (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ f = f)
    (transitive : ∀ x y : V.obj.left, f.hom.left x = f.hom.left y →
      ∃ g : G, (action g).asIso.hom.hom.left x = y) :
    ∀ x y : (closedCoverPullbackSquare f i j).X₁.obj.left,
      (closedCoverPullbackCube f i j).τ₁.hom.left x =
        (closedCoverPullbackCube f i j).τ₁.hom.left y →
          ∃ g : G,
            ((closedCoverPullbackSquareAction f i j action over_base).on1 g).asIso.hom.hom.left x =
              y := by
  have closed := @closedImmersionSquare_first_isClosedImmersion S V
    (closedImmersionPullback f i) (closedImmersionPullback f j)
    (closedImmersionSquare f i).f₁₂ (closedImmersionSquare f j).f₁₂
    (closedImmersionSquare_first_isClosedImmersion f j)
  exact fiberTransitivity_of_injective_square (closedImmersionSquare f i).f₁₃
    (closedCoverPullbackCube f i j).τ₁ (closedCoverPullbackSquare f i j).f₁₂
    (closedImmersionSquare i j).f₁₂ (closedCoverPullbackCube f i j).comm₁₂
    (closedBaseChangeAction f i action over_base)
    (closedCoverPullbackSquareAction f i j action over_base).on1
    (closedCoverPullbackSquareAction f i j action over_base).equivariant12
    (@IsClosedImmersion.isClosedEmbedding _ _ _ closed).injective
    (closedBaseChangeAction_transitive_on_fibers f i action over_base transitive)

/-- 概要：両側を被約化した交わりの指定射にも元の切断から軌道被覆を得る（定理 3.1）。
方針：構成した切断と推移性を被約化関手で移し、移動切断の被覆判定を使う。
規約：被約化後の幾何条件を別の仮定にせず、元の切断と推移性から導く。
使われ方：非被約な交わりを低次元の被約な場合の帰納へ入力する。 -/
theorem closedCoverIntersection_reduced_covering {G : Type u} [Group G]
    (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ f = f)
    (transitive : ∀ x y : V.obj.left, f.hom.left x = f.hom.left y →
      ∃ g : G, (action g).asIso.hom.hom.left x = y)
    (s : B ⟶ V) (hs : s ≫ f = 𝟙 B) :
    ⋃ t : TranslatedSectionIndex
        (finiteTypeReductionAction (closedCoverPullbackSquareAction f i j action over_base).on1)
        (finiteTypeReductionMap (closedCoverIntersectionSection f i j s hs)),
      Set.range t.val.hom.left = Set.univ :=
  translatedSection_covering (finiteTypeReductionMap (closedCoverPullbackCube f i j).τ₁) _
    (finiteTypeReductionMap_section _ _ (closedCoverIntersectionSection_identity f i j s hs)) _
    (finiteTypeReductionAction_transitive_on_fibers _ _
      (closedCoverIntersection_transitive_on_fibers f i j action over_base transitive))

end SerrePositivity.KST.Descent
