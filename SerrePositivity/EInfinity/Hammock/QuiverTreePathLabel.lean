module

public import SerrePositivity.EInfinity.Hammock.QuiverTreeDetector

/-!
# 木の全射列の群値ラベル

概要：木の実際の射列は検出表現で単位へ写る。
方針：射列の連結と正・逆の各生成辺で帰納する。
規約：元の部分 quiver の所属証明を使う。
使われ方：薄さによって木の外の辺を排除する。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.QuiverTree
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))

lemma path_label {x y : T} (p : Quiver.Path x y) :
    labelValue T ((evaluation T).map p) = 1 := by
  induction p with
  | nil =>
    change labelValue T ((evaluation T).map (𝟙 _)) = 1
    exact (congrArg (labelValue T) ((evaluation T).map_id ((Paths.of T).obj x))).trans
      (labelValue_id T _)
  | @cons y z p e ih =>
    have hc := (evaluation T).map_comp p e.toPath
    change labelValue T ((evaluation T).map (p ≫ e.toPath)) = 1
    rw [hc, labelValue_comp, ih, mul_one]
    rcases e with ⟨e | e, he⟩
    · rw [evaluation_positive, labelValue_generator]
      exact edgeLabel_of_mem T e (Or.inl he)
    · rw [evaluation_negative, labelValue_inv, labelValue_generator,
        edgeLabel_of_mem T e (Or.inr he), inv_one]

variable [Quiver.Arborescence T]

def rootHom (x : T) :
    (Quiver.FreeGroupoid.of Q).obj (Quiver.root T) ⟶ (Quiver.FreeGroupoid.of Q).obj x :=
  (evaluation T).map (default : Quiver.Path (Quiver.root T) x)

lemma rootHom_label (x : T) : labelValue T (rootHom T x) = 1 :=
  path_label T _

end SerrePositivity.EInfinity.Hammock.QuiverTree
