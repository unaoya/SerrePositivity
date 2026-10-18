module

public import SerrePositivity.KST.Descent.PresheafBaseChange

/-!
# 自然な transfer の底変換の幾何比較

## 概要
元の射の底変換と、基底上で制限した後の底変換を、第一射影を保つ自然同型で比較する。

## 方針
二重の実際の引き戻しの二射影を指定し、普遍性で逆と自然性を証明する。

## 規約
元の選択された引き戻しを使い、transfer や rank 公式はこの段階で仮定しない。

## 使われ方
論文 補題 3.2 の有限平坦 transfer を各基底変更へ制限する幾何入力。
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y)

/-- 概要：基底変更後の二重引き戻しと元の引き戻しの指定同型（補題 3.2）。
方針：元の二射影から入れ子の引き戻しへ lift し、逆に内側の第一射影へ合成する。
規約：第一射影は元の基底上の対象への射。使われ方：自然な transfer の制限。 -/
def transferBaseChangeStageIso (T : Over Z) :
    pullback (T.hom ≫ g) f ≅ pullback T.hom (pullback.snd f g) where
  hom := pullback.lift (pullback.fst (T.hom ≫ g) f)
    (pullback.lift (pullback.snd (T.hom ≫ g) f)
      (pullback.fst (T.hom ≫ g) f ≫ T.hom)
      (by simpa only [Category.assoc] using
        (pullback.condition (f := T.hom ≫ g) (g := f)).symm))
    (pullback.lift_snd _ _ _).symm
  inv := pullback.lift (pullback.fst T.hom (pullback.snd f g))
    (pullback.snd T.hom (pullback.snd f g) ≫ pullback.fst f g)
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ g) (pullback.condition (f := T.hom) (g := pullback.snd f g))).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (pullback.snd T.hom (pullback.snd f g) ≫ ·)
            (pullback.condition (f := f) (g := g)).symm).trans (Category.assoc _ _ _).symm))))
  hom_inv_id := by
    apply pullback.hom_ext <;> simp
  inv_hom_id := by
    apply pullback.hom_ext
    · simp
    · apply pullback.hom_ext <;> simp [pullback.condition]

/-- 概要：指定二重引き戻し同型は元の第一射影を保つ（補題 3.2）。
方針：外側 lift の第一射影公式。規約：指定された同型の hom の式。
使われ方：元の前層の pullback 自然変換との整合性。 -/
theorem transferBaseChangeStageIso_hom_fst (T : Over Z) :
    (transferBaseChangeStageIso f g T).hom ≫ pullback.fst T.hom (pullback.snd f g) =
      pullback.fst (T.hom ≫ g) f := pullback.lift_fst _ _ _

/-- 概要：二重引き戻しの指定同型は基底上の全射に自然（補題 3.2）。
方針：外側と内側の二射影で pullback の射の公式を検査する。
規約：対象ごとの同型の存在に弱めない。使われ方：前層の自然な比較同型。 -/
theorem transferBaseChangeStageIso_naturality {T T' : Over Z} (a : T ⟶ T') :
    (((Over.map g ⋙ overBaseChange f) ⋙ Over.forget Y).map a) ≫
        (transferBaseChangeStageIso f g T').hom =
      (transferBaseChangeStageIso f g T).hom ≫
        ((overBaseChange (pullback.snd f g) ⋙ Over.forget Z).map a) := by
  apply pullback.hom_ext
  · simp [transferBaseChangeStageIso, overBaseChange, Over.pullback]
  · apply pullback.hom_ext <;>
      simp [transferBaseChangeStageIso, overBaseChange, Over.pullback, Over.w]

/-- 概要：制限と底変換の二つの実際の幾何関手の指定自然同型（補題 3.2）。
方針：二重引き戻しの指定同型と全射の自然性を束ねる。
規約：元の第一射影との可換式も保持。使われ方：元の前層による transfer の制限。 -/
def transferBaseChangeGeometryIso :
    (Over.map g ⋙ overBaseChange f) ⋙ Over.forget Y ≅
      overBaseChange (pullback.snd f g) ⋙ Over.forget Z :=
  NatIso.ofComponents (transferBaseChangeStageIso f g)
    (fun a ↦ transferBaseChangeStageIso_naturality f g a)

end SerrePositivity.KST.Descent
