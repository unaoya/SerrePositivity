module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeZigzagFunctor
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingHom

/-!
# 相対自然変換の元の全頂点への適用

概要：全成分が指定射である自然変換を同じ語の行の縦比較へ移す。
方針：各列と元の縦射に自然性を適用し、端点の成分を異種等式で保持する。
規約：端点の成分は恒等射と仮定しない。
使われ方：外側の二列と貼って固定端点の比較を作る。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.RelativeNatural
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {F G : LocalizerMorphism W V} (η : F.functor ⟶ G.functor)
  (hη : ∀ X, V (η.app X)) {w : Word} {X Y : C}

omit [W.IsMultiplicative] [V.IsMultiplicative] in
lemma component_heq {A B : C} (h : A = B) : HEq (η.app A) (η.app B) := by
  subst B
  rfl

def movingHom (S : Zigzag W w X Y) :
    Zigzag.MovingHom (Zigzag.Relative.obj F S) (Zigzag.Relative.obj G S) where
  app j := η.app (S.vertex j)
  app_mem j := hη (S.vertex j)
  comm i := η.naturality (S.arrow i)

omit [W.IsMultiplicative] [V.IsMultiplicative] in
lemma movingHom_first (S : Zigzag W w X Y) :
    HEq ((movingHom η hη S).app 0) (η.app X) := component_heq η S.first

omit [W.IsMultiplicative] [V.IsMultiplicative] in
lemma movingHom_last (S : Zigzag W w X Y) :
    HEq ((movingHom η hη S).app (Fin.last w.length)) (η.app Y) := component_heq η S.last

lemma movingHom_naturality {S T : Zigzag W w X Y} (f : S ⟶ T) :
    (Zigzag.MovingHom.ofHom (Zigzag.Relative.map F f)).comp (movingHom η hη T) =
      (movingHom η hη S).comp (Zigzag.MovingHom.ofHom (Zigzag.Relative.map G f)) := by
  apply Zigzag.MovingHom.ext
  intro j
  exact η.naturality (f.app j)

end SerrePositivity.EInfinity.Hammock.RelativeNatural
