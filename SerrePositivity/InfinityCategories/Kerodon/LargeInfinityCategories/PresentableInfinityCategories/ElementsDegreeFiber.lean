module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Adjunction.Comma
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NerveFinalInitialComma

/-!
概要：要素圏の次数射影に沿う左 Kan 延長を、離散ファイバーへ縮約する。
方針：comma の対象を指定次数へ押し出し、ファイバー包含との随伴を構成する。
規約：通常の関手の全射と全ての要素を保持する。
使われ方：前層 bar 構成の各次数の小余積の比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u v w
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {I : Type v} [Category.{w} I] (X : I ⥤ Type u) (i : I)

/-- 概要：要素圏の次数ファイバーを同じ左 Kan comma へ入れる。
方針：指定次数の各要素に恒等底射を付ける。
規約：全ての要素を含み、有限性を要求しない。
使われ方：次数ごとの余積図式の cofinal な比較。 -/
def elementsDegreeFiber : Discrete (X.obj i) ⥤ CostructuredArrow (Functor.Elements.π X) i :=
  Discrete.functor (fun s ↦ CostructuredArrow.mk (Y := X.elementsMk i s) (𝟙 i))

/-- 概要：左 Kan comma の対象を指定次数の同じ要素へ押し出す。
方針：底射に沿う元の型値関手の作用を用いる。
規約：comma の可換三角形により射の作用を定める。
使われ方：離散ファイバー包含の左随伴。 -/
def elementsDegreePush : CostructuredArrow (Functor.Elements.π X) i ⥤ Discrete (X.obj i) where
  obj a := Discrete.mk (X.map a.hom a.left.val)
  map {a b} f := eqToHom (by
    apply Discrete.ext
    change X.map a.hom a.left.val = X.map b.hom b.left.val
    have hw : f.left.hom ≫ b.hom = a.hom := f.w
    rw [← hw, X.map_comp]
    change X.map b.hom (X.map f.left.hom a.left.val) = _
    rw [f.left.map_val])

/-- 概要：指定次数のファイバー対象への comma の射は一意。
方針：可換三角形が底射を元の指定射に固定する。
規約：一般の底圏の射を離散と仮定しない。
使われ方：ファイバー縮約の全自然性。 -/
lemma elementsDegreeFiber_hom_ext
    {a : CostructuredArrow (Functor.Elements.π X) i} {s : Discrete (X.obj i)}
    (f g : a ⟶ (elementsDegreeFiber X i).obj s) : f = g := by
  apply CostructuredArrow.hom_ext
  apply Functor.Elements.Hom.ext
  have hf : f.left.hom = a.hom := by simpa [elementsDegreeFiber] using f.w
  have hg : g.left.hom = a.hom := by simpa [elementsDegreeFiber] using g.w
  exact hf.trans hg.symm

/-- 概要：指定次数への押し出しは、同じ離散ファイバー包含の左随伴。
方針：元の底射に沿う要素の輸送条件と、離散圏の等式を全自然に比較する。
規約：元の comma と次数を固定する。
使われ方：各 bar 次数の小余積を計算する final 性。 -/
def elementsDegreeAdjunction : elementsDegreePush X i ⊣ elementsDegreeFiber X i :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun a s ↦ {
      toFun := fun f ↦ CostructuredArrow.homMk
        (show a.left ⟶ X.elementsMk i s.as from
          { hom := a.hom
            map_val := Discrete.eq_of_hom f }) (by simp [elementsDegreeFiber])
      invFun := fun f ↦ eqToHom (by
        apply Discrete.ext
        have hw : f.left.hom = a.hom := by simpa [elementsDegreeFiber] using f.w
        change X.map a.hom a.left.val = s.as
        rw [← hw]
        exact f.left.map_val)
      left_inv := fun _ ↦ Subsingleton.elim _ _
      right_inv := fun f ↦ elementsDegreeFiber_hom_ext X i _ f }
    homEquiv_naturality_left_symm := fun _ _ ↦ Subsingleton.elim _ _
    homEquiv_naturality_right := fun _ _ ↦ elementsDegreeFiber_hom_ext X i _ _ }

/-- 概要：同じ次数の離散ファイバーは左 Kan comma で final。
方針：構成した左随伴から final 性を得る。
規約：追加の余極限存在仮定を要求しない。
使われ方：bar の各次数を表現可能の小余積として読む。 -/
lemma elementsDegreeFiber_final : (elementsDegreeFiber X i).Final :=
  Functor.final_of_adjunction (elementsDegreeAdjunction X i)

/-- 概要：同じ離散次数ファイバーの nerve は、元の comma で right cofinal。
方針：構成した左随伴の単位が与える各始対象を native な Quillen 判定へ渡す。
規約：通常の final 性だけで止めず、全高次の cofinal 性を与える。
使われ方：coherent な前層値 bar の各次数の余積計算。 -/
lemma elementsDegreeFiber_nerve_isRightCofinal
    {J : Type u} [Category.{u} J] (Y : J ⥤ Type u) (j : J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (nerveMap (elementsDegreeFiber Y j)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nerveMap_isRightCofinal_of_initial_comma
  intro a
  let adj := elementsDegreeAdjunction Y j
  exact ⟨StructuredArrow.mk (adj.unit.app a),
    ⟨mkInitialOfLeftAdjoint (elementsDegreeFiber Y j) adj a⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
