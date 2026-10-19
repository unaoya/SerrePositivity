module

public import SerrePositivity.KST.DerivedBlowup.DiagramModuleCoefficientCategory

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の係数図式の射を図式加群の係数 dg 関手へ移す。
方針：各 Hom で行先代数の成分を使い、自然性とモノイド射の積保存で合成則を示す。
規約：原典と異なる図式 dg 加群模型の比較。対象の添字は変えない。
使われ方：例外因子の二つの係数表示から得る加群模型の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory DifferentialGraded

/-- 概要：可換な係数代数の四角形は遷移後の乗法と可換。
方針：行先の積保存と四角形の等式を tensor の関手性で組み合わせる。
規約：KST §3.1 の一般モノイダル補題。使われ方：係数 dg 関手の合成保存。 -/
theorem diagramAlgebraMul_square {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {A B A' B' : Mon C} (f : A ⟶ B) (g : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : f ≫ b = a ≫ g) :
    diagramAlgebraMul f ≫ b.hom = (a.hom ⊗ₘ b.hom) ≫ diagramAlgebraMul g := by
  have hh : f.hom ≫ b.hom = a.hom ≫ g.hom := congrArg Mon.Hom.hom h
  unfold diagramAlgebraMul
  rw [Category.assoc, IsMonHom.mul_hom, ← Category.assoc, tensorHom_comp_tensorHom]
  simp only [Category.id_comp, hh]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [Category.comp_id]

variable {R : Type u} [CommRing R] {J : Type w} [Preorder J] [DecidableLE J]
variable {F G : J ⥤ Mon (Complex R)} (α : F ⟶ G)

/-- 概要：係数図式の射から各 Hom 複体の写像を作る。
方針：包含上では行先代数の成分を使い、包含がなければ零複体の標準同定とする。
規約：KST §3.1。使われ方：係数図式の dg 関手。 -/
def diagramCoefficientHomMap (i j : J) : diagramModuleHom F i j ⟶ diagramModuleHom G i j :=
  if h : i ≤ j then eqToHom (diagramModuleHom_of_le F h) ≫
    (α.app j).hom ≫ diagramModuleHomInclusion G h
  else eqToHom (by simp only [diagramModuleHom, ite_eq_right h])

/-- 概要：包含に沿う係数 Hom 写像は行先代数の成分そのもの。
方針：Hom の標準同定の順逆を消去する。
規約：KST §3.1。使われ方：単位・合成の具体的計算。 -/
theorem diagramCoefficientHomMap_inclusion {i j : J} (h : i ≤ j) :
    diagramModuleHomInclusion F h ≫ diagramCoefficientHomMap α i j =
      (α.app j).hom ≫ diagramModuleHomInclusion G h := by
  simp only [diagramCoefficientHomMap, dite_eq_left h, diagramModuleHomInclusion,
    ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

set_option maxHeartbeats 2000000 in
-- 二つの係数図式の Hom 同定と豊穣合成を照合するために必要。
/-- 概要：係数図式の自然変換は図式加群の係数 dg 圏の関手を誘導する。
方針：添字を固定し、行先代数の成分の単位・積保存と自然性で圏法則を示す。
規約：KST §3.1・Lemma 3.6。使われ方：係数表示の変更と局所射の加群への作用。 -/
def diagramCoefficientDGFunctor :
    DGFunctor R (DiagramModuleCoefficientObject F) (DiagramModuleCoefficientObject G) where
  obj x := ⟨x.index⟩
  map x y := diagramCoefficientHomMap α x.index y.index
  map_id x := by
    change diagramModuleId F x.index ≫ diagramCoefficientHomMap α x.index x.index =
      diagramModuleId G x.index
    simp only [diagramModuleId]
    rw [Category.assoc, diagramCoefficientHomMap_inclusion, ← Category.assoc,
      IsMonHom.one_hom]
  map_comp x y z := by
    change diagramModuleComp F x.index y.index z.index ≫
        diagramCoefficientHomMap α x.index z.index =
      (diagramCoefficientHomMap α x.index y.index ⊗ₘ
        diagramCoefficientHomMap α y.index z.index) ≫
          diagramModuleComp G x.index y.index z.index
    by_cases h : x.index ≤ y.index
    · by_cases g : y.index ≤ z.index
      · let : IsIso (diagramModuleHomInclusion F h) := by
          unfold diagramModuleHomInclusion
          infer_instance
        let : IsIso (diagramModuleHomInclusion F g) := by
          unfold diagramModuleHomInclusion
          infer_instance
        apply (cancel_epi (diagramModuleHomInclusion F h ⊗ₘ
          diagramModuleHomInclusion F g)).mp
        rw [← Category.assoc, diagramModuleComp_on_le, Category.assoc,
          Category.assoc, diagramCoefficientHomMap_inclusion,
          tensorHom_comp_tensorHom_assoc, diagramCoefficientHomMap_inclusion,
          diagramCoefficientHomMap_inclusion, ← tensorHom_comp_tensorHom_assoc,
          diagramModuleComp_on_le]
        simpa only [diagramAlgebraMul, Category.assoc] using
          congrArg (fun f => f ≫ diagramModuleHomInclusion G (h.trans g))
            (diagramAlgebraMul_square (F.map (homOfLE g)) (G.map (homOfLE g))
              (α.app y.index) (α.app z.index) (α.naturality (homOfLE g)))
      · simp only [diagramModuleComp, dite_eq_left h, dite_eq_right g,
          Limits.zero_comp, Limits.comp_zero]
    · simp only [diagramModuleComp, dite_eq_right h, Limits.zero_comp, Limits.comp_zero]

end SerrePositivity.KST.DerivedBlowup
