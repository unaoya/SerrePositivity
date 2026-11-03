module
public import SerrePositivity.DifferentialGraded.Module.Graded
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-! # 元の Yoneda 評価と斉次合成
概要：代表加群からの斉次射の合成を、元の単位での評価として計算する。
方針：元の moduleHom end の合成成分と Yoneda 評価の定義を使う。
規約：全次数と Koszul 符号を保持。使われ方：元の gluing 第三成分の合成保存。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]

/-- 元の Yoneda 評価で、二斉次射の豊穣合成の符号をそのまま回収する。 -/
lemma dgHomGluingYoneda_forward (x : E) (M N : RightModule R E) {r s t : ℤ}
    (a : (moduleHom R E (representable R x) M).X r)
    (b : (moduleHom R E M N).X s) (ht : r + s = t) :
    (dgYonedaIso R x N).hom.f t
        (forward R (x := representable R x) (y := M) (z := N) a b ht) =
      (r * s).negOnePow •
        (((moduleHomπ R E M N x).f s b).v r t ht)
          ((dgYonedaIso R x M).hom.f r a) := by
  dsimp only [dgYonedaIso]
  rw [yonedaEvaluateFamily_apply, moduleHomForward_π]
  change (r * s).negOnePow •
    ((((moduleHomπ R E (representable R x) M x).f r a).comp
      ((moduleHomπ R E M N x).f s b) ht).v 0 t (zero_add _))
      (unitElement R x).val = _
  rw [Cochain.comp_v _ _ _ 0 r t (zero_add r) ht, yonedaEvaluateFamily_apply]
  rfl

/-- 元の Yoneda 逆写像の任意の評価成分を、同じ右加群作用に戻す。 -/
lemma dgHomGluingYoneda_inv_element (x y : E) (M : RightModule R E) {r s t : ℤ}
    (a : (M.obj (op x)).X s) (f : GradedHom R y x r) (ht : r + s = t) :
    (((moduleHomπ R E (representable R x) M y).f s
      ((dgYonedaIso R x M).inv.f s a)).v r t ht) f =
      (s * r).negOnePow •
        moduleAction R M (x := op x) (y := op y) f a (by omega) := by
  have hp := moduleHomEquiv_symm_π R E (M.obj (op x)) (representable R x) M
    (yonedaExtension R x M (𝟙 _)) y
  change (dgYonedaIso R x M).inv ≫ moduleHomπ R E (representable R x) M y =
    yonedaExtensionApp R x M (𝟙 _) (op y) at hp
  have he := congrArg (fun z => (z.f s a).v r t ht f) hp
  change _ = _ at he
  exact he.trans (by
    simpa only [HomologicalComplex.id_f, ModuleCat.id_apply] using
      yonedaExtensionApp_apply R x M (𝟙 _) (op y) s r t ht a f)

/-- 同じ Yoneda 逆像を元の評価で戻すと、元の斉次値を回収する。 -/
lemma dgHomGluingYoneda_inv_hom (x : E) (M : RightModule R E) (n : ℤ)
    (a : (M.obj (op x)).X n) :
    (dgYonedaIso R x M).hom.f n ((dgYonedaIso R x M).inv.f n a) = a :=
  ConcreteCategory.congr_hom
    (congrArg (fun f => f.f n) (dgYonedaIso R x M).inv_hom_id) a

end SerrePositivity.KST.SConstruction
