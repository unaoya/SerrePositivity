module

public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Localization.Opposite
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.HomCongr

/-!
# 局所化左関手の右随伴から元の右関手の右導来普遍性へ

概要：Hovey §1.3 の導来随伴の右関手を自然変換の普遍性で特徴付ける。
方針：前合成随伴の Hom 対応と局所化による完全忠実性を合成する。
規約：元の右関手が弱同値を保つことやモデル構造を仮定しない。
使われ方：元の通常極限からの比較を持つ homotopy 極限の右導来性。
-/

@[expose] public section

noncomputable section

universe uC vC uD vD uH vH uJ vJ

namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.AdjointRightDerived

open CategoryTheory Functor

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {H : Type uH} [Category.{vH} H] {J : Type uJ} [Category.{vJ} J]
  {G : C ⥤ D} {F : D ⥤ C} (adj : G ⊣ F)
  (Q : C ⥤ H) (W : MorphismProperty C) [Q.IsLocalization W]
  (R : D ⥤ J) {G' : H ⥤ J} {F' : J ⥤ H} (adj' : G' ⊣ F')
  (c : Q ⋙ G' ≅ G ⋙ R)
/-- 概要：導来右随伴からの自然変換の普遍的な同値（Hovey §1.3）。
方針：二つの前合成随伴と局所化の完全忠実性を合成する。
規約：元の左関手の局所化比較を保持する。
使われ方：右導来関手の自然変換の普遍性。 -/
def transformationEquiv (T : J ⥤ H) : (F' ⟶ T) ≃ (F ⋙ Q ⟶ R ⋙ T) :=
  ((adj'.whiskerLeft H).homEquiv (𝟭 H) T).trans
    (((Localization.fullyFaithfulWhiskeringLeft Q W H).homEquiv).trans
      ((Iso.homCongr (Q.leftUnitor) ((Functor.associator Q G' T).symm ≪≫
        isoWhiskerRight c T ≪≫ Functor.associator G R T)).trans
          ((adj.whiskerLeft H).homEquiv Q (R ⋙ T)).symm))
/-- 概要：自然変換の同値の各成分を元の余単位で計算（Hovey §1.3）。
方針：前合成随伴の単位・余単位と自然性を展開する。
規約：元の随伴と局所化随伴の同じ成分。
使われ方：実際の計算関手の比較射との照合。 -/
lemma transformationEquiv_app (T : J ⥤ H) (g : F' ⟶ T) (Y : D) :
    (transformationEquiv adj Q W R adj' c T g).app Y =
      adj'.unit.app (Q.obj (F.obj Y)) ≫
        F'.map (c.hom.app (F.obj Y) ≫ R.map (adj.counit.app Y)) ≫ g.app (R.obj Y) := by
  simp only [transformationEquiv, Equiv.trans_apply,
    Iso.homCongr, Equiv.coe_fn_mk, Functor.FullyFaithful.homEquiv_apply]
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_unit]
  dsimp
  simp only [Adjunction.whiskerLeft_unit_app_app, Adjunction.whiskerLeft_counit_app_app,
    Functor.id_map, Category.id_comp, Category.comp_id, Category.assoc, Functor.map_comp]
  change adj'.unit.app _ ≫ g.app _ ≫ T.map (c.hom.app _) ≫
    T.map (R.map (adj.counit.app Y)) = _
  rw [← g.naturality_assoc, ← g.naturality]
  rfl


/-- 概要：元の右関手から局所化右随伴への比較（Hovey §1.3）。
方針：自然変換の同値で右随伴の恒等射を移す。
規約：元の随伴と左関手の比較のみから作る。
使われ方：右導来普遍性を持つ比較の正規化。 -/
def comparison : F ⋙ Q ⟶ R ⋙ F' :=
  transformationEquiv adj Q W R adj' c F' (𝟙 F')

/-- 概要：自然変換の同値は比較への後合成（Hovey §1.3）。
方針：各成分の式を恒等自然変換の場合と比較する。
規約：局所化後の任意の候補関手を許す。
使われ方：Kan 拡張の普遍性の構成。 -/
lemma transformationEquiv_eq (T : J ⥤ H) (g : F' ⟶ T) :
    transformationEquiv adj Q W R adj' c T g = comparison adj Q W R adj' c ≫ whiskerLeft R g := by
  ext Y
  simp only [NatTrans.comp_app, whiskerLeft_app, comparison, transformationEquiv_app,
    NatTrans.id_app,
    Category.assoc]
  exact congrArg (fun z => adj'.unit.app (Q.obj (F.obj Y)) ≫
    F'.map (c.hom.app (F.obj Y) ≫ R.map (adj.counit.app Y)) ≫ z)
      (Category.id_comp (g.app (R.obj Y))).symm

/-- 概要：局所化右随伴は元の右関手の左 Kan 拡張（Hovey §1.3）。
方針：自然変換の同値で拡張圏の一意な射を構成する。
規約：モデル構造や右関手の弱同値保存は仮定しない。
使われ方：元の比較を持つ右導来関手の普遍性。 -/
theorem isLeftKanExtension : F'.IsLeftKanExtension (comparison adj Q W R adj' c) := by
  refine ⟨⟨?_⟩⟩
  refine Limits.IsInitial.ofUniqueHom
    (fun y => StructuredArrow.homMk
      ((transformationEquiv adj Q W R adj' c y.right).symm y.hom) ?_) ?_
  · change comparison adj Q W R adj' c ≫
      whiskerLeft R ((transformationEquiv adj Q W R adj' c y.right).symm y.hom) = y.hom
    rw [← transformationEquiv_eq, Equiv.apply_symm_apply]
  · intro y m
    apply StructuredArrow.hom_ext
    apply (transformationEquiv adj Q W R adj' c y.right).injective
    rw [transformationEquiv_eq]
    exact m.w.trans ((transformationEquiv adj Q W R adj' c y.right).apply_symm_apply _).symm
/-- 概要：比較射は元の余単位の局所化随伴像（Hovey §1.3）。
方針：成分計算の恒等射を相殺し Hom 随伴の式へ戻す。
規約：同じ比較を保ち、新しい比較射を選ばない。
使われ方：元の極限比較との一致。 -/
lemma comparison_app (Y : D) : (comparison adj Q W R adj' c).app Y =
    adj'.homEquiv (Q.obj (F.obj Y)) (R.obj Y)
      (c.hom.app (F.obj Y) ≫ R.map (adj.counit.app Y)) := by
  rw [comparison, transformationEquiv_app, adj'.homEquiv_unit]
  exact congrArg (fun z => adj'.unit.app (Q.obj (F.obj Y)) ≫ z)
    (Category.comp_id (F'.map (c.hom.app (F.obj Y) ≫ R.map (adj.counit.app Y))))

/-- 概要：同じ比較を持つ局所化右随伴は右導来関手（Hovey §1.3）。
方針：証明した左 Kan 拡張の普遍性を右導来関手に束ねる。
規約：始域と終域の局所化だけを要求し、モデル構造は不要。
使われ方：一般小図式の具体的な E 代数 homotopy 極限。 -/
theorem isRightDerivedFunctor (V : MorphismProperty D) [R.IsLocalization V] :
    F'.IsRightDerivedFunctor (comparison adj Q W R adj' c) V :=
  ⟨isLeftKanExtension adj Q W R adj' c⟩

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.AdjointRightDerived
