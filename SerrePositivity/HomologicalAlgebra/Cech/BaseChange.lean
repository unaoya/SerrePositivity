module

public import Mathlib.AlgebraicTopology.CechNerve
public import SerrePositivity.HomologicalAlgebra.Cech.Basic
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.Algebra.Category.Ring.Under.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
概要：可換環の増大 Čech 余脈体と底変換。
方針：各項を基底環の下の圏での余積として比較し、加群のテンソル積の完全性を使う。
規約：通常のテンソル積を使う。保存には平坦性、反映には忠実平坦性を仮定する。
使われ方：平坦な拡大上で得られた Čech 完全性を元の基底上で判定する。
-/

@[expose] public section
noncomputable section

universe u
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SerrePositivity.Cech

set_option backward.isDefEq.respectTransparency false

variable {A : CommRingCat.{u}}

/-- 環の Čech 余脈体を基底環の下の圏に持ち上げる。 -/
def underCech (B : Under A) : CosimplicialObject.Augmented (Under A) where
  left := Under.mk (𝟙 A)
  right :=
    { obj := fun n => Under.mk ((Arrow.mk B.hom).augmentedCechConerve.hom.app n)
      map := fun φ => Under.homMk ((Arrow.mk B.hom).cechConerve.map φ) (by
        have h := (Arrow.mk B.hom).augmentedCechConerve.hom.naturality φ
        exact h.symm.trans (Category.id_comp _))
      map_id := by
        intro n
        ext : 1
        exact (Arrow.mk B.hom).cechConerve.map_id n
      map_comp := by
        intro i j k φ ψ
        ext : 1
        exact (Arrow.mk B.hom).cechConerve.map_comp φ ψ }
  hom :=
    { app := fun n => Under.homMk ((Arrow.mk B.hom).augmentedCechConerve.hom.app n) (by simp)
      naturality := by
        intro i j φ
        exact (Under.mkIdInitial (X := A)).hom_ext _ _ }

@[simp]
theorem underCech_forget (B : Under A) :
    (CosimplicialObject.Augmented.whiskeringObj _ _ (Under.forget A)).obj (underCech B) =
      (Arrow.mk B.hom).augmentedCechConerve := by
  rfl

/-- 各次数の余脈体への挿入を、基底上の余積の脚とみなす。 -/
def underCechInclusion (B : Under A) (n : SimplexCategory) (i : Fin (n.len + 1)) :
    B ⟶ (underCech B).right.obj n :=
  Under.homMk (WidePushout.ι (fun _ : Fin (n.len + 1) => B.hom) i)
    (WidePushout.arrow_ι (fun _ : Fin (n.len + 1) => B.hom) i)

@[reassoc]
theorem underCechInclusion_naturality (B : Under A) {m n : SimplexCategory} (φ : m ⟶ n)
    (i : Fin (m.len + 1)) :
    underCechInclusion B m i ≫ (underCech B).right.map φ =
      underCechInclusion B n (φ.toOrderHom i) := by
  ext : 1
  exact WidePushout.ι_desc (fun _ : Fin (m.len + 1) => B.hom) _ _ _ i

/-- 基底の下の圏で、余脈体の各項は有限余積である。 -/
def underCechCofan (B : Under A) (n : SimplexCategory) :
    Cofan (fun _ : Fin (n.len + 1) => B) :=
  Cofan.mk _ (underCechInclusion B n)

/-- 余脈体の広い押し出しの普遍性を、基底上の余積の普遍性として読む。 -/
def underCechCofanIsColimit (B : Under A) (n : SimplexCategory) :
    IsColimit (underCechCofan B n) := by
  refine Cofan.IsColimit.mk _ (fun s => Under.homMk
    (WidePushout.desc s.pt.hom (fun i => (s.inj i).right) (fun i => Under.w (s.inj i))) ?_) ?_ ?_
  · exact WidePushout.head_desc (fun _ : Fin (n.len + 1) => B.hom) _ _ _
  · intro s j
    ext : 1
    exact WidePushout.ι_desc (fun _ : Fin (n.len + 1) => B.hom) _ _ _ j
  · intro s m hm
    ext : 1
    let arrows : Fin (n.len + 1) → (A ⟶ B.right) := fun _ => B.hom
    let fs (i : Fin (n.len + 1)) := (s.inj i).right
    let w (i : Fin (n.len + 1)) : arrows i ≫ fs i = s.pt.hom := Under.w (s.inj i)
    change m.right = WidePushout.desc s.pt.hom fs w
    apply WidePushout.hom_ext
    · intro i
      exact (congrArg Under.Hom.right (hm i)).trans
        (WidePushout.ι_desc arrows s.pt.hom fs w i).symm
    · exact (Under.w m).trans (WidePushout.head_desc arrows s.pt.hom fs w).symm

variable {D : CommRingCat.{u}}

/-- 余積を保つ関手で移した余脈体の余積表示。 -/
def mappedCofanIsColimit (F : Under A ⥤ Under D) [PreservesColimitsOfSize.{0, 0} F]
    (B : Under A) (n : SimplexCategory) :
    IsColimit (Cofan.mk _ (fun i => F.map (underCechInclusion B n i)) :
      Cofan (fun _ : Fin (n.len + 1) => F.obj B)) :=
  isColimitCofanMkObjOfIsColimit F _ _ (underCechCofanIsColimit B n)

/-- 各次数の余積比較。 -/
def underCechObjIso (F : Under A ⥤ Under D) [PreservesColimitsOfSize.{0, 0} F]
    (B : Under A) (n : SimplexCategory) :
    F.obj ((underCech B).right.obj n) ≅ (underCech (F.obj B)).right.obj n :=
  (mappedCofanIsColimit F B n).coconePointUniqueUpToIso
    (underCechCofanIsColimit (F.obj B) n)

@[reassoc]
theorem underCechObjIso_fac (F : Under A ⥤ Under D) [PreservesColimitsOfSize.{0, 0} F]
    (B : Under A) (n : SimplexCategory) (i : Fin (n.len + 1)) :
    F.map (underCechInclusion B n i) ≫ (underCechObjIso F B n).hom =
      underCechInclusion (F.obj B) n i :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (mappedCofanIsColimit F B n)
    (underCechCofanIsColimit (F.obj B) n) ⟨i⟩

/-- 余積と始対象を保つ基底変換は増大 Čech 余脈体と可換する。 -/
def underCechMapIso (F : Under A ⥤ Under D) [PreservesColimitsOfSize.{0, 0} F] (B : Under A) :
    (CosimplicialObject.Augmented.whiskeringObj _ _ F).obj (underCech B) ≅
      underCech (F.obj B) := by
  let h := (Under.mkIdInitial (X := A)).isInitialObj F
  refine Comma.isoMk (h.uniqueUpToIso (Under.mkIdInitial (X := D)))
    (NatIso.ofComponents (underCechObjIso F B) ?_) ?_
  · intro m n φ
    apply (mappedCofanIsColimit F B m).hom_ext
    rintro ⟨i⟩
    change F.map (underCechInclusion B m i) ≫
        F.map ((underCech B).right.map φ) ≫ (underCechObjIso F B n).hom =
      F.map (underCechInclusion B m i) ≫
        (underCechObjIso F B m).hom ≫ (underCech (F.obj B)).right.map φ
    rw [← F.map_comp_assoc, underCechInclusion_naturality, underCechObjIso_fac,
      underCechObjIso_fac_assoc, underCechInclusion_naturality]
  · apply NatTrans.ext
    funext n
    exact h.hom_ext _ _

end SerrePositivity.Cech

namespace SerrePositivity.Cech

open MonoidalCategory

set_option backward.isDefEq.respectTransparency false

variable {A : CommRingCat.{u}}

/-- 基底環の下の可換環から、その基底上の加群を取る。 -/
def underToModule (A : CommRingCat.{u}) : Under A ⥤ ModuleCat.{u} A where
  obj B := ModuleCat.of A B
  map f := ModuleCat.ofHom (CommRingCat.toAlgHom f).toLinearMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 基底変換で用いるテンソル積の関手は余極限を保つ。 -/
theorem tensorProd_preservesColimits (A D : CommRingCat.{u}) [Algebra A D] :
    PreservesColimitsOfSize.{0, 0} (CommRingCat.tensorProd A D) := by
  let := (Under.mapPushoutAdj (CommRingCat.ofHom (algebraMap A D))).isRightAdjoint
  exact preservesColimits_of_natIso (CommRingCat.tensorProdIsoPushout A D).symm

/-- 加群として作った増大 Čech 複体。 -/
def moduleCech (B : Under A) : CochainComplex (ModuleCat.{u} A) ℕ :=
  augmentedCochain.obj
    ((CosimplicialObject.Augmented.whiskeringObj _ _ (underToModule A)).obj (underCech B))

theorem moduleCech_acyclic_iff (B : Under A) :
    (moduleCech B).Acyclic ↔ IsCechExact (Arrow.mk B.hom) := by
  rw [show IsCechExact (Arrow.mk B.hom) ↔
      (ringCochain.obj (Arrow.mk B.hom).augmentedCechConerve).Acyclic from
    ringCechExact_iff_acyclic _]
  let F := forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}
  have hF : ∀ S : ShortComplex (ModuleCat.{u} A), (S.map F).Exact ↔ S.Exact := by
    intro S
    rw [ShortComplex.ab_exact_iff_function_exact,
      ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    rfl
  rw [← acyclic_map_iff_of_exact F _ hF]
  let e := mapAugmentedCochainIso F
    ((CosimplicialObject.Augmented.whiskeringObj _ _ (underToModule A)).obj (underCech B))
  have e' : _ ≅ ringCochain.obj (Arrow.mk B.hom).augmentedCechConerve := e
  exact ⟨fun h n => (h n).of_iso e', fun h n => (h n).of_iso e'.symm⟩

variable (D : CommRingCat.{u}) [Algebra A D]

/-- 底変換後の Čech 複体は、元の Čech 複体の項ごとのテンソル積。 -/
def baseChangeCochainIso (B : Under A) :
    (((tensorLeft (ModuleCat.of A D) ⋙ forget₂ (ModuleCat A) AddCommGrpCat).mapHomologicalComplex
      (.up ℕ)).obj (moduleCech B)) ≅
    ringCochain.obj (Arrow.mk ((CommRingCat.tensorProd A D).obj B).hom).augmentedCechConerve := by
  let F := tensorLeft (ModuleCat.of A D) ⋙ forget₂ (ModuleCat A) AddCommGrpCat
  let T := CommRingCat.tensorProd A D
  let U := Under.forget D ⋙ ringToAb
  let X := (CosimplicialObject.Augmented.whiskeringObj _ _ (underToModule A)).obj (underCech B)
  letI := tensorProd_preservesColimits A D
  let e := underCechMapIso T B
  let q : underToModule A ⋙ F ≅ T ⋙ U := NatIso.ofComponents
    (fun _ => Iso.refl _) (by
      intro P Q f
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      rfl)
  let eq := (CosimplicialObject.Augmented.whiskering _ _).mapIso q
  refine mapAugmentedCochainIso F X ≪≫ ?_
  let e₂ := augmentedCochain.mapIso (eq.app (underCech B))
  let e₃ := augmentedCochain.mapIso
    ((CosimplicialObject.Augmented.whiskeringObj _ _ U).mapIso e)
  exact e₂ ≪≫ e₃

private theorem baseChange_iff_map_acyclic (B : Under A) :
    IsCechExact (Arrow.mk ((CommRingCat.tensorProd A D).obj B).hom) ↔
      (((tensorLeft (ModuleCat.of A D) ⋙ forget₂ (ModuleCat A) AddCommGrpCat).mapHomologicalComplex
        (.up ℕ)).obj (moduleCech B)).Acyclic := by
  change AugmentedRingCechExact _ ↔ _
  rw [ringCechExact_iff_acyclic]
  let e := baseChangeCochainIso D B
  exact ⟨fun h n => (h n).of_iso e.symm, fun h n => (h n).of_iso e⟩

/-- 平坦な底変換は増大 Čech 完全性を保つ。 -/
theorem isCechExact_baseChange (B : Under A) [Module.Flat A D]
    (h : IsCechExact (Arrow.mk B.hom)) :
    IsCechExact (Arrow.mk ((CommRingCat.tensorProd A D).obj B).hom) := by
  apply (baseChange_iff_map_acyclic D B).mpr
  intro n
  rw [HomologicalComplex.exactAt_iff]
  exact (Module.Flat.lTensor_shortComplex_exact (ModuleCat.of A D) _
    ((moduleCech_acyclic_iff B).mpr h n)).map (forget₂ (ModuleCat A) AddCommGrpCat)

/-- 忠実平坦な底変換は増大 Čech 完全性を反映する。 -/
theorem isCechExact_baseChange_iff (B : Under A) [Module.FaithfullyFlat A D] :
    IsCechExact (Arrow.mk ((CommRingCat.tensorProd A D).obj B).hom) ↔
      IsCechExact (Arrow.mk B.hom) := by
  rw [baseChange_iff_map_acyclic, ← moduleCech_acyclic_iff B]
  apply acyclic_map_iff_of_exact
  intro S
  rw [ShortComplex.ab_exact_iff_function_exact,
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  exact Module.FaithfullyFlat.lTensor_exact_iff_exact A D (l12 := S.f.hom) (l23 := S.g.hom)

end SerrePositivity.Cech
