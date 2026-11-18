module

public import SerrePositivity.CategoryTheory.CechNerveData

/-!
概要：指定 Čech 脈体の有限冪への射を、各座標の指定射から作る。
方針：CechNerveData の積錐の元の普遍性だけを用いる。
  文献対応：HTT 4.1.3.1、Kerodon Theorem 7.2.3.1（Tag 02NY）の Čech comma の収縮。
規約：有限積一般の存在を追加せず、元の指定された冪と射影を保持する。
-/

@[expose] public noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [Category.{v} C] {U V W : C}

/-- 指定した有限個の座標射を、元の Čech 冪への射へ束ねる。 -/
def cechPowerLift (d : CategoryTheory.CechNerveData U) {n : ℕ}
    (g : Fin (n + 1) → (V ⟶ U)) : V ⟶ d.obj.obj (Opposite.op ⦋n⦌) :=
  (d.isLimit n).lift (Fan.mk V g)

/-- 束ねた射の指定座標は元の射そのもの。 -/
lemma cechPowerLift_proj (d : CategoryTheory.CechNerveData U) {n : ℕ}
    (g : Fin (n + 1) → (V ⟶ U)) (i : Fin (n + 1)) :
    cechPowerLift d g ≫ d.proj n i = g i :=
  (d.isLimit n).fac (Fan.mk V g) ⟨i⟩

/-- 指定冪への射は全座標で決まる。 -/
lemma cechPower_hom_ext (d : CategoryTheory.CechNerveData U) {n : ℕ}
    {f g : V ⟶ d.obj.obj (Opposite.op ⦋n⦌)}
    (h : ∀ i, f ≫ d.proj n i = g ≫ d.proj n i) : f = g := by
  apply (d.isLimit n).hom_ext
  intro i
  exact h i.as

/-- 射を全座標から回収すると元の射へ戻る。 -/
lemma cechPowerLift_proj_eq (d : CategoryTheory.CechNerveData U) {n : ℕ}
    (f : V ⟶ d.obj.obj (Opposite.op ⦋n⦌)) :
    cechPowerLift d (fun i ↦ f ≫ d.proj n i) = f := by
  apply cechPower_hom_ext d
  intro i
  exact cechPowerLift_proj d _ i

/-- 座標射の束縛は源の射との合成を保つ。 -/
lemma cechPowerLift_precomp (d : CategoryTheory.CechNerveData U) {n : ℕ}
    (f : W ⟶ V) (g : Fin (n + 1) → (V ⟶ U)) :
    f ≫ cechPowerLift d g = cechPowerLift d (fun i ↦ f ≫ g i) := by
  apply cechPower_hom_ext d
  intro i
  simp only [Category.assoc, cechPowerLift_proj]

/-- 元の単体射で冪を移すと、座標の再添字に一致する。 -/
lemma cechPowerLift_map (d : CategoryTheory.CechNerveData U) {m n : ℕ}
    (θ : ⦋m⦌ ⟶ ⦋n⦌) (g : Fin (n + 1) → (V ⟶ U)) :
    cechPowerLift d g ≫ d.obj.map θ.op =
      cechPowerLift d (fun i ↦ g (θ.toOrderHom i)) := by
  apply cechPower_hom_ext d
  intro i
  rw [Category.assoc, d.proj_map, cechPowerLift_proj, cechPowerLift_proj]

end SerrePositivity.InfinityCategories.Sheaves
