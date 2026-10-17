module

public import SerrePositivity.CategoryTheory.ArrowFactorizationCategory

/-!
# 因子分解圏の外側の射に沿う移送が合成と整合する

## 概要
因子分解圏の外側の射に沿う移送が合成と整合する。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
中間対象と二つの因子を明示し、射には左右の三角形の可換性を要求する。
恒等・合成・移送をこのデータ上で定義し、成分の一意性から法則を導く。

## 規約と注意
圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
表示された圏や比較射を、局所化後の同型だけで置き換えない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はS-構成に現れる圏のnerve、射列、図式間の自然なホモトピーに利用できる。
[棚卸し m0008][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../formalization-plans/k-theory-generalization-inventory.md#m0008
[plan]: ../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual external transport of factorization categories

External arrows change only the two legs. The middle objects and maps are
retained. A fixed target composite keeps the laws as equalities of actual
functors, with the associativity equation recorded in the data.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory

namespace SerrePositivity.ArrowFactorization
variable {D : Type u} [Category.{v} D] {Y V Y' V' : D} (g : Y ⟶ V)

def preTo (a : Y' ⟶ Y) (h : Y' ⟶ V) (e : a ≫ g = h) :
    ArrowFactorization g ⥤ ArrowFactorization h where
  obj p := ⟨p.middle, a ≫ p.left, p.right, by rw [Category.assoc, p.fac, e]⟩
  map f := ⟨f.hom, by rw [Category.assoc, f.left_comm], f.right_comm⟩

def postTo (b : V ⟶ V') (h : Y ⟶ V') (e : g ≫ b = h) :
    ArrowFactorization g ⥤ ArrowFactorization h where
  obj p := ⟨p.middle, p.left, p.right ≫ b, by rw [← Category.assoc, p.fac, e]⟩
  map f := ⟨f.hom, f.left_comm, by rw [← Category.assoc, f.right_comm]⟩

def transport (a : Y' ⟶ Y) (b : V ⟶ V') (h : Y' ⟶ V') (e : (a ≫ g) ≫ b = h) :
    ArrowFactorization g ⥤ ArrowFactorization h where
  obj p :=
    { middle := p.middle
      left := a ≫ p.left
      right := p.right ≫ b
      fac := by
        calc
          _ = (a ≫ (p.left ≫ p.right)) ≫ b := by simp only [Category.assoc]
          _ = (a ≫ g) ≫ b := congrArg (fun q => (a ≫ q) ≫ b) p.fac
          _ = h := e }
  map f := ⟨f.hom, by rw [Category.assoc, f.left_comm],
    by rw [← Category.assoc, f.right_comm]⟩

lemma transport_forget (a : Y' ⟶ Y) (b : V ⟶ V') (h : Y' ⟶ V') (e : (a ≫ g) ≫ b = h) :
    transport g a b h e ⋙ forget h = forget g := rfl

lemma transport_id : transport g (𝟙 Y) (𝟙 V) g (by simp) = 𝟭 (ArrowFactorization g) := by
  have ho (p : ArrowFactorization g) :
      (transport g (𝟙 Y) (𝟙 V) g (by simp)).obj p = p := by
    change ArrowFactorization.mk p.middle ((𝟙 Y) ≫ p.left) (p.right ≫ 𝟙 V) _ = p
    simp only [Category.id_comp, Category.comp_id]
  refine CategoryTheory.Functor.ext ho ?_
  intro p q f
  apply Hom.ext
  simp only [comp_hom, eqToHom_hom, eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

lemma context_comp {Y'' V'' : D} (a : Y' ⟶ Y) (b : V ⟶ V') (h : Y' ⟶ V')
    (e : (a ≫ g) ≫ b = h) (a' : Y'' ⟶ Y') (b' : V' ⟶ V'') (k : Y'' ⟶ V'')
    (e' : (a' ≫ h) ≫ b' = k) : (((a' ≫ a) ≫ g) ≫ (b ≫ b')) = k := by
  calc
    _ = (a' ≫ ((a ≫ g) ≫ b)) ≫ b' := by simp only [Category.assoc]
    _ = (a' ≫ h) ≫ b' := congrArg (fun q => (a' ≫ q) ≫ b') e
    _ = k := e'

/-- 因子分解圏の外側の射に沿う移送が合成と整合する。

圏・対象・射の宇宙と必要な極限の仮定は各宣言に従う。
中間対象と二つの因子を明示し、射には左右の三角形の可換性を要求する。
恒等・合成・移送をこのデータ上で定義し、成分の一意性から法則を導く。
-/
lemma transport_comp {Y'' V'' : D} (a : Y' ⟶ Y) (b : V ⟶ V') (h : Y' ⟶ V')
    (e : (a ≫ g) ≫ b = h) (a' : Y'' ⟶ Y') (b' : V' ⟶ V'') (k : Y'' ⟶ V'')
    (e' : (a' ≫ h) ≫ b' = k) :
    transport g a b h e ⋙ transport h a' b' k e' =
      transport g (a' ≫ a) (b ≫ b') k (context_comp g a b h e a' b' k e') := by
  have ho (p : ArrowFactorization g) :
      (transport h a' b' k e').obj ((transport g a b h e).obj p) =
        (transport g (a' ≫ a) (b ≫ b') k (context_comp g a b h e a' b' k e')).obj p := by
    change ArrowFactorization.mk p.middle (a' ≫ (a ≫ p.left)) ((p.right ≫ b) ≫ b') _ =
      ArrowFactorization.mk p.middle ((a' ≫ a) ≫ p.left) (p.right ≫ (b ≫ b')) _
    congr 1
    · exact (Category.assoc _ _ _).symm
    · exact Category.assoc _ _ _
  refine CategoryTheory.Functor.ext ho ?_
  intro p q f
  apply Hom.ext
  simp only [comp_hom, eqToHom_hom, eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- Actual external pre- and postcomposition commute, with the target arrow fixed. -/
lemma pre_post (a : Y' ⟶ Y) (b : V ⟶ V') (h : Y' ⟶ V') (e : (a ≫ g) ≫ b = h) :
    preTo g a (a ≫ g) rfl ⋙ postTo (a ≫ g) b h e =
      postTo g b (g ≫ b) rfl ⋙
        preTo (g ≫ b) a h ((Category.assoc a g b).symm.trans e) := rfl

lemma pre_post_transport (a : Y' ⟶ Y) (b : V ⟶ V') (h : Y' ⟶ V')
    (e : (a ≫ g) ≫ b = h) :
    preTo g a (a ≫ g) rfl ⋙ postTo (a ≫ g) b h e = transport g a b h e := rfl

end SerrePositivity.ArrowFactorization
