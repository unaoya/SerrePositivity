module

public import SerrePositivity.Spectra.SymmetricSequence.FreeConvolution

/-! # 自由convolutionの生成元からの降下

第一ブロックの作用の関係式を満たす生成元上の射の族を、各段全体の射へ一意に延長する。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  [HasColimitsOfSize.{0, 0} C]

/-- 第一ブロックの全単射の関係式を満たす、生成元上の射の族。 -/
structure FreeConvolutionFamily (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) (Y : C) where
  app (a : FiniteBijection)
    (h : FiniteBijection.sumObj a (FiniteBijection.of n) ⟶ FiniteBijection.of m) : F.obj a ⊗ X ⟶ Y
  relation {a b : FiniteBijection} (k : a ⟶ b)
    (h : FiniteBijection.sumObj b (FiniteBijection.of n) ⟶ FiniteBijection.of m) :
    F.map k ▷ X ≫ app b h = app a (FiniteBijection.sumMap k (𝟙 _) ≫ h)

variable {F : SymmetricSequence C} {n m : ℕ} {X Y : C}

namespace FreeConvolutionFamily

/-- 各段全体の射を生成元へ制限する。 -/
def ofHom (f : level (convolution F ((freeAt n).obj X)) m ⟶ Y) :
    FreeConvolutionFamily F n X m Y where
  app a h := freeConvolutionGenerator F n X m a h ≫ f
  relation k h := by
    rw [← Category.assoc, freeConvolutionGenerator_left_relation]

omit [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] in
/-- 射の族は各生成元での値で決まる。 -/
@[ext] lemma ext (s t : FreeConvolutionFamily F n X m Y)
    (h : ∀ a k, s.app a k = t.app a k) : s = t := by
  cases s
  cases t
  congr
  funext a k
  exact h a k

variable (s : FreeConvolutionFamily F n X m Y)

/-- 余積保存によって、射の族を各分解項へ延長する。 -/
def component (d : CostructuredArrow FiniteBijection.sumFunctor (FiniteBijection.of m)) :
    (freeConvolutionDiagram F n X m).obj d ⟶ Y :=
  (isColimitOfPreserves (tensorLeft (F.obj d.left.1))
    (colimit.isColimit (Discrete.functor (fun _ : FiniteBijection.of n ⟶ d.left.2 => X)))).desc
      { pt := Y
        ι.app k := s.app d.left.1 (FiniteBijection.sumMap (𝟙 _) k.as ≫ d.hom)
        ι.naturality i j f := by
          have hij : i = j := Discrete.ext (Discrete.eq_of_hom (X := i) (Y := j) f)
          subst j
          have hf : f = 𝟙 i := Subsingleton.elim _ _
          subst f
          simp }

/-- 各分解項への延長は余積成分上で指定された値に一致する。 -/
@[reassoc] lemma component_fac
    (d : CostructuredArrow FiniteBijection.sumFunctor (FiniteBijection.of m))
    (k : FiniteBijection.of n ⟶ d.left.2) :
    F.obj d.left.1 ◁ freeAtInclusion n X k ≫ s.component d =
      s.app d.left.1 (FiniteBijection.sumMap (𝟙 _) k ≫ d.hom) := by
  exact (isColimitOfPreserves (tensorLeft (F.obj d.left.1))
    (colimit.isColimit (Discrete.functor (fun _ : FiniteBijection.of n ⟶ d.left.2 => X)))).fac
      _ ⟨k⟩

/-- 各分解項への延長は、分解図式の射と両立する。 -/
lemma component_naturality
    {d e : CostructuredArrow FiniteBijection.sumFunctor (FiniteBijection.of m)} (φ : d ⟶ e) :
    (freeConvolutionDiagram F n X m).map φ ≫ s.component e = s.component d := by
  apply (isColimitOfPreserves (tensorLeft (F.obj d.left.1))
    (colimit.isColimit (Discrete.functor (fun _ : FiniteBijection.of n ⟶ d.left.2 => X)))).hom_ext
  intro k
  change (F.obj d.left.1 ◁ freeAtInclusion n X k.as) ≫
    (((F.map φ.left.1 ▷ _) ≫ (F.obj e.left.1 ◁ ((freeAt n).obj X).map φ.left.2)) ≫
      s.component e) = (F.obj d.left.1 ◁ freeAtInclusion n X k.as) ≫ s.component d
  simp only [Category.assoc]
  erw [whisker_exchange_assoc, ← whiskerLeft_comp_assoc, freeAtInclusion_map,
    component_fac, component_fac, s.relation]
  congr 1
  rw [← Category.assoc, FiniteBijection.sumMap_comp]
  simp only [Category.comp_id, Category.id_comp]
  have hh : FiniteBijection.sumMap (𝟙 d.left.1) k.as ≫
      FiniteBijection.sumMap φ.left.1 φ.left.2 =
        FiniteBijection.sumMap φ.left.1 (k.as ≫ φ.left.2) := by
    rw [FiniteBijection.sumMap_comp, Category.id_comp]
  erw [← hh, Category.assoc, CostructuredArrow.w φ]

/-- 射の族から得られる、分解図式上の余錐。 -/
def cocone : Cocone (freeConvolutionDiagram F n X m) where
  pt := Y
  ι.app d := s.component d
  ι.naturality d e φ := by
    simpa using s.component_naturality φ

/-- 関係式を満たす射の族を、第m段全体の射へ降ろす。 -/
def desc : level (convolution F ((freeAt n).obj X)) m ⟶ Y :=
  (freeConvolutionLevelIsoColimit F n X m).hom ≫
    colimit.desc (freeConvolutionDiagram F n X m) s.cocone

/-- 降下した射は各生成元上で指定された値に一致する。 -/
@[reassoc] lemma desc_fac (a : FiniteBijection)
    (h : FiniteBijection.sumObj a (FiniteBijection.of n) ⟶ FiniteBijection.of m) :
    freeConvolutionGenerator F n X m a h ≫ s.desc = s.app a h := by
  let d : CostructuredArrow FiniteBijection.sumFunctor (FiniteBijection.of m) :=
    CostructuredArrow.mk (Y := (a, FiniteBijection.of n)) h
  have hi : (convolutionUnit F ((freeAt n).obj X)).app (a, FiniteBijection.of n) ≫
      (convolution F ((freeAt n).obj X)).map h ≫
        (freeConvolutionLevelIsoColimit F n X m).hom =
          colimit.ι (freeConvolutionDiagram F n X m) d :=
    Functor.ι_leftKanExtensionObjIsoColimit_hom FiniteBijection.sumFunctor
      (externalProduct F ((freeAt n).obj X)) (FiniteBijection.of m) d
  simp only [freeConvolutionGenerator, desc, Category.assoc]
  erw [reassoc_of% hi, colimit.ι_desc]
  change F.obj a ◁ freeAtGenerator n X ≫ s.component d = s.app a h
  have hf := s.component_fac d (𝟙 (FiniteBijection.of n))
  change F.obj a ◁ freeAtGenerator n X ≫ s.component d =
    s.app a (FiniteBijection.sumMap (𝟙 a) (𝟙 (FiniteBijection.of n)) ≫ h) at hf
  erw [FiniteBijection.sumMap_id, Category.id_comp] at hf
  exact hf

/-- 各生成元での値が指定された射は、上の降下と一致する。 -/
lemma desc_unique (f : level (convolution F ((freeAt n).obj X)) m ⟶ Y)
    (h : ∀ a k, freeConvolutionGenerator F n X m a k ≫ f = s.app a k) : f = s.desc := by
  apply freeConvolutionLevel_hom_ext
  intro a k
  rw [s.desc_fac]
  exact h a k

end FreeConvolutionFamily

/-- 自由convolutionの各段からの射と、関係式を満たす生成元上の射の族との同値。 -/
def freeConvolutionLevelHomEquiv (F : SymmetricSequence C) (n : ℕ) (X : C) (m : ℕ) (Y : C) :
    (level (convolution F ((freeAt n).obj X)) m ⟶ Y) ≃ FreeConvolutionFamily F n X m Y where
  toFun := FreeConvolutionFamily.ofHom
  invFun := FreeConvolutionFamily.desc
  left_inv f := (FreeConvolutionFamily.desc_unique _ f (fun _ _ => rfl)).symm
  right_inv s := by
    apply FreeConvolutionFamily.ext
    intro a k
    exact s.desc_fac a k

end SerrePositivity.SymmetricSequence
