module
public import SerrePositivity.KST.SConstruction.PointedLiftTransport

/-! # 持ち上げ空間の移送の関手法則
概要：持ち上げ空間の全パラメーターへの移送は恒等・合成を保つ。
方針：写像空間への射影と一点への射影で検証する。
規約：厳密等号でありホモトピー類だけの主張ではない。
使われ方：混合切断空間の前後合成と高次境界の貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet

/-- 恒等正方形による持ち上げ空間の移送は恒等射。 -/
lemma pointedLiftTransport_id {A E B : PointedSimplicialSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) :
    pointedLiftTransport p b p b (𝟙 A) (𝟙 E) (𝟙 B) (by simp) (by simp) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [pointedLiftTransport_projection, pointedMappingTransport_id,
      Category.comp_id, Category.id_comp]
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _

/-- 持ち上げ空間の移送の合成は合成正方形の移送になる。 -/
lemma pointedLiftTransport_comp {A E B A' E' B' A'' E'' B'' : PointedSimplicialSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (p' : E' ⟶ B') (b' : A' ⟶ B')
    (p'' : E'' ⟶ B'') (b'' : A'' ⟶ B'')
    (a : A' ⟶ A) (e : E ⟶ E') (c : B ⟶ B')
    (a' : A'' ⟶ A') (e' : E' ⟶ E'') (c' : B' ⟶ B'')
    (hp : e ≫ p' = p ≫ c) (hb : a ≫ b ≫ c = b')
    (hp' : e' ≫ p'' = p' ≫ c') (hb' : a' ≫ b' ≫ c' = b'')
    (hpp : (e ≫ e') ≫ p'' = p ≫ (c ≫ c'))
    (hbb : (a' ≫ a) ≫ b ≫ (c ≫ c') = b'') :
    pointedLiftTransport p b p' b' a e c hp hb ≫
      pointedLiftTransport p' b' p'' b'' a' e' c' hp' hb' =
    pointedLiftTransport p b p'' b'' (a' ≫ a) (e ≫ e') (c ≫ c') hpp hbb := by
  apply pullback.hom_ext
  · rw [Category.assoc, pointedLiftTransport_projection, ← Category.assoc,
      pointedLiftTransport_projection, Category.assoc, pointedMappingTransport_comp,
      pointedLiftTransport_projection]
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _

end SerrePositivity.KST.SConstruction
