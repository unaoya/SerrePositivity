module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.LeftRoofPrecomposeLowerInsertion

/-!
# 先頭の恒等列を除いた元の三列

概要：X→V←U→Y とその全縦弱同値を同じ三列にまとめる。
方針：四頂点と全可換正方形を直接保持する。
規約：中央の backward のみ弱同値を要求し、元の hammock の語を使う。
使われ方：始点変更に対する roof 全円柱の厳密な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v uI vI
namespace SerrePositivity.EInfinity.Hammock.ForwardRoof
open CategoryTheory
abbrev word := LeftRoof.Precompose.preWord
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X Y V U V' U' : C}

def obj (a : X ⟶ V) (p : U ⟶ V) (hp : W p) (σ : U ⟶ Y) : Zigzag W word X Y where
  vertex := ![X, V, U, Y]
  first := rfl
  last := rfl
  arrow := Fin.cases a (Fin.cases p (Fin.cases σ (fun i => Fin.elim0 i)))
  backward_mem i hi := by
    fin_cases i
    · cases hi
    · exact hp
    · cases hi

def map {a : X ⟶ V} {p : U ⟶ V} {hp : W p} {σ : U ⟶ Y}
    {a' : X ⟶ V'} {p' : U' ⟶ V'} {hp' : W p'} {σ' : U' ⟶ Y}
    (r : V ⟶ V') (hr : W r) (s : U ⟶ U') (hs : W s)
    (ha : a ≫ r = a') (hpq : p ≫ r = s ≫ p') (hσ : σ = s ≫ σ') :
    obj W a p hp σ ⟶ obj W a' p' hp' σ' where
  app := Fin.cases (𝟙 X) (Fin.cases r (Fin.cases s
    (Fin.cases (𝟙 Y) (fun i => Fin.elim0 i))))
  app_mem j := by
    fin_cases j
    · exact W.id_mem X
    · exact hr
    · exact hs
    · exact W.id_mem Y
  first := rfl
  last := rfl
  comm j := by
    fin_cases j
    · exact ha.trans (Category.id_comp _).symm
    · exact hpq
    · exact (Category.comp_id _).trans hσ

omit [W.IsMultiplicative] in
lemma append_obj (a : X ⟶ V) (p : U ⟶ V) (hp : W p) (σ : U ⟶ Y) :
    ZigzagAppend.obj (ForwardZigzag.obj (W := W) a) (LeftRoof.obj W p hp σ) =
      obj W a p hp σ := by
  apply Zigzag.object_ext
  · intro j
    fin_cases j <;> rfl
  · intro j
    fin_cases j
    · exact ZigzagAppend.arrow_left_heq (ForwardZigzag.obj a) (LeftRoof.obj W p hp σ) (0 : Fin 1)
    · exact ZigzagAppend.arrow_right_heq (ForwardZigzag.obj a) (LeftRoof.obj W p hp σ) (0 : Fin 2)
    · exact ZigzagAppend.arrow_right_heq (ForwardZigzag.obj a) (LeftRoof.obj W p hp σ) (1 : Fin 2)

lemma insert_obj (a : X ⟶ V) (p : U ⟶ V) (hp : W p) (σ : U ⟶ Y) :
    WordAction.obj LeftRoof.Precompose.lowerInsert (obj W a p hp σ) =
      LeftRoof.Precompose.lower W p hp a σ := by
  rw [← append_obj]
  exact LeftRoof.Precompose.lowerInsert_obj W p hp a σ

variable {I : Type uI} [Category.{vI} I]
  (V U : I ⥤ C) (a : (Functor.const I).obj X ⟶ V) (p : U ⟶ V)
  (hp : ∀ i, W (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hV : ∀ {i j} (f : i ⟶ j), W (V.map f))
  (hU : ∀ {i j} (f : i ⟶ j), W (U.map f))

def diagram : I ⥤ Zigzag W word X Y where
  obj i := obj W (a.app i) (p.app i) (hp i) (σ.app i)
  map {i j} f := map W (V.map f) (hV f) (U.map f) (hU f)
    ((a.naturality f).symm.trans (Category.id_comp _))
    (p.naturality f).symm
    ((σ.naturality f).trans (Category.comp_id _)).symm
  map_id i := Zigzag.hom_ext _ _ (by
    intro j
    fin_cases j
    · rfl
    · exact V.map_id i
    · exact U.map_id i
    · rfl)
  map_comp f g := Zigzag.hom_ext _ _ (by
    intro j
    fin_cases j
    · exact (Category.id_comp _).symm
    · exact V.map_comp f g
    · exact U.map_comp f g
    · exact (Category.id_comp _).symm)

end SerrePositivity.EInfinity.Hammock.ForwardRoof
