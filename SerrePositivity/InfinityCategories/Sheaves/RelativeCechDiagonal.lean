module

public import SerrePositivity.InfinityCategories.Sheaves.RelativeCechDiagram

/-!
概要：同じ相対 Čech 冪への対角の全自然変換と、元の各座標での分裂を保つ。
方針：既存 cechPowerLift の単体作用素と射影の計算則を使う。
規約：HTT 6.2.2.6 の Čech 解消への通常圏の入力。零次を含む全次数を扱う。
使われ方：S8 の局所単射から各 Čech 冪への局所全射を示すための同じ対角。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [Category.{v} C] {P Q : C}
variable (f : P ⟶ Q) [HasFiniteProducts (Over Q)]

/-- 元の全座標に恒等射を束ねた、相対 Čech 図式への同じ対角。 -/
def relativeCechDiagonal : (Functor.const (AsSmall.{v} SimplexCategoryᵒᵖ)).obj P ⟶
    relativeCechDiagram f where
  app n := (cechPowerLift (relativeCechData f)
    (n := (AsSmall.down.obj n).unop.len) (fun _ => 𝟙 (Over.mk f))).left
  naturality {i j} θ := by
    have h := cechPowerLift_map (relativeCechData f) (AsSmall.down.map θ).unop
      (fun _ => 𝟙 (Over.mk f))
    change 𝟙 P ≫ _ = _
    rw [Category.id_comp]
    exact (congrArg CommaMorphism.left h).symm

/-- 同じ対角の各座標は元の恒等射。 -/
lemma relativeCechDiagonal_proj (n : AsSmall.{v} SimplexCategoryᵒᵖ)
    (i : Fin ((AsSmall.down.obj n).unop.len + 1)) :
    (relativeCechDiagonal f).app n ≫
      ((relativeCechData f).proj (AsSmall.down.obj n).unop.len i).left = 𝟙 P :=
  congrArg CommaMorphism.left
    (cechPowerLift_proj (relativeCechData f) (fun _ => 𝟙 (Over.mk f)) i)

/-- 最初の元の座標が、全ての次数で同じ対角の明示的な左逆射になる。 -/
def relativeCechDiagonalSplitMono (n : AsSmall.{v} SimplexCategoryᵒᵖ) :
    SplitMono ((relativeCechDiagonal f).app n) where
  retraction := ((relativeCechData f).proj (AsSmall.down.obj n).unop.len 0).left
  id := relativeCechDiagonal_proj f n 0

/-- 対角は零次を含む全ての次数で単射。 -/
instance relativeCechDiagonal_isSplitMono (n : AsSmall.{v} SimplexCategoryᵒᵖ) :
    IsSplitMono ((relativeCechDiagonal f).app n) :=
  ⟨⟨relativeCechDiagonalSplitMono f n⟩⟩

/-- 忘却した同じ相対 Čech 冪への射は、元の全座標だけで決まる。 -/
lemma relativeCech_proj_hom_ext (n : ℕ) {V : C}
    {h k : V ⟶ ((relativeCechData f).obj.obj (Opposite.op ⦋n⦌)).left}
    (he : ∀ i : Fin (n + 1), h ≫ ((relativeCechData f).proj n i).left =
      k ≫ ((relativeCechData f).proj n i).left) : h = k := by
  let r := h ≫ ((relativeCechData f).obj.obj (Opposite.op ⦋n⦌)).hom
  have hw : ((relativeCechData f).proj n 0).left ≫ f =
      ((relativeCechData f).obj.obj (Opposite.op ⦋n⦌)).hom :=
    Over.w ((relativeCechData f).proj n 0)
  have hk : k ≫ ((relativeCechData f).obj.obj (Opposite.op ⦋n⦌)).hom = r := by
    dsimp only [r]
    rw [← hw, ← Category.assoc, ← he 0, Category.assoc]
  have hl := cechPower_hom_ext (relativeCechData f)
    (f := (Over.homMk h rfl : Over.mk r ⟶ _))
    (g := (Over.homMk k hk : Over.mk r ⟶ _)) (fun i => by
      apply Over.OverMorphism.ext
      exact he i)
  exact congrArg CommaMorphism.left hl

end SerrePositivity.InfinityCategories.Sheaves
