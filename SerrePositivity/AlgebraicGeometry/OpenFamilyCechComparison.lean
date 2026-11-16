module

public import SerrePositivity.AlgebraicGeometry.FiniteFamilyCechComponents
public import SerrePositivity.AlgebraicGeometry.SchemeCechTupleCover

/-!
概要：元の開の混合積を、元の nerve の同じタプル開へ移す。
方針：元の射影と開埋め込みへの一意な持ち上げで正逆を取る。
規約：元の射、開、入射を保持し、アフィン性を要求しない。
使われ方：矩形タプルの実際の構造層の係数比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite TopologicalSpace
universe u
variable {Y S : Scheme.{u}} (f : Y ⟶ S) {ι : Type} (U : ι → Y.Opens)

/-- 元の開の混合積から、元の射の nerve への標準射。 -/
def openFamilyCechInclusion (n : SimplexCategory) (t : Fin (n.len + 1) → ι) :
    finiteFamilyCechComponent (fun i ↦ (U i).ι ≫ f) n t ⟶
      (Arrow.mk f).cechNerve.obj (op n) :=
  WidePullback.lift (WidePullback.base (fun j ↦ (U (t j)).ι ≫ f))
    (fun j ↦ WidePullback.π (fun j ↦ (U (t j)).ι ≫ f) j ≫ (U (t j)).ι)
    (fun j ↦ by
      change (WidePullback.π (fun j ↦ (U (t j)).ι ≫ f) j ≫ (U (t j)).ι) ≫ f = _
      rw [Category.assoc, WidePullback.π_arrow])

/-- 元の各射影との合成は、同じ開の入射。 -/
theorem openFamilyCechInclusion_π (n : SimplexCategory) (t : Fin (n.len + 1) → ι)
    (j : Fin (n.len + 1)) :
    openFamilyCechInclusion f U n t ≫ WidePullback.π (fun _ : Fin (n.len + 1) ↦ f) j =
      WidePullback.π (fun j ↦ (U (t j)).ι ≫ f) j ≫ (U (t j)).ι :=
  WidePullback.lift_π _ _ _ _ j

/-- 元の基底への射も保つ。 -/
theorem openFamilyCechInclusion_base (n : SimplexCategory) (t : Fin (n.len + 1) → ι) :
    openFamilyCechInclusion f U n t ≫ WidePullback.base (fun _ : Fin (n.len + 1) ↦ f) =
      WidePullback.base (fun j ↦ (U (t j)).ι ≫ f) :=
  WidePullback.lift_base _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- 同じ標準射の像は、元のタプル開に入る。 -/
theorem openFamilyCechInclusion_range (n : SimplexCategory) (t : Fin (n.len + 1) → ι) :
    Set.range (openFamilyCechInclusion f U n t) ⊆
      Set.range (schemeCechTupleOpen f U (op n) t).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  change openFamilyCechInclusion f U n t x ∈
    ((⨅ j, WidePullback.π (fun _ : Fin (n.len + 1) ↦ f) j ⁻¹ᵁ U (t j)) : Opens _)
  rw [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  intro j
  have he := congrArg (fun g ↦ (g : _ ⟶ Y) x) (openFamilyCechInclusion_π f U n t j)
  change (openFamilyCechInclusion f U n t ≫
    WidePullback.π (fun _ : Fin (n.len + 1) ↦ f) j) x ∈ U (t j)
  rw [he]
  exact (WidePullback.π (fun j ↦ (U (t j)).ι ≫ f) j x).property

/-- 元の入射を因子化する、同じタプル開への標準射。 -/
def openFamilyCechToOpen (n : SimplexCategory) (t : Fin (n.len + 1) → ι) :
    finiteFamilyCechComponent (fun i ↦ (U i).ι ≫ f) n t ⟶
      (schemeCechTupleOpen f U (op n) t).toScheme :=
  IsOpenImmersion.lift (schemeCechTupleOpen f U (op n) t).ι
    (openFamilyCechInclusion f U n t) (openFamilyCechInclusion_range f U n t)

/-- 同じ開への標準射は、元の混合積からの入射を因子化する。 -/
theorem openFamilyCechToOpen_fac (n : SimplexCategory) (t : Fin (n.len + 1) → ι) :
    openFamilyCechToOpen f U n t ≫ (schemeCechTupleOpen f U (op n) t).ι =
      openFamilyCechInclusion f U n t :=
  IsOpenImmersion.lift_fac _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- 同じタプル開の各射影を、元の開へ一意に持ち上げる。 -/
def openFamilyCechProjection (n : SimplexCategory) (t : Fin (n.len + 1) → ι)
    (j : Fin (n.len + 1)) :
    (schemeCechTupleOpen f U (op n) t).toScheme ⟶ (U (t j)).toScheme :=
  IsOpenImmersion.lift (U (t j)).ι
    ((schemeCechTupleOpen f U (op n) t).ι ≫
      WidePullback.π (fun _ : Fin (n.len + 1) ↦ f) j) (by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨x, rfl⟩
        exact (iInf_le (fun k ↦ WidePullback.π (fun _ : Fin (n.len + 1) ↦ f) k ⁻¹ᵁ U (t k)) j)
          x.property)

/-- 同じ射影の持ち上げは、元の開への入射と可換。 -/
theorem openFamilyCechProjection_fac (n : SimplexCategory) (t : Fin (n.len + 1) → ι)
    (j : Fin (n.len + 1)) :
    openFamilyCechProjection f U n t j ≫ (U (t j)).ι =
      (schemeCechTupleOpen f U (op n) t).ι ≫
        WidePullback.π (fun _ : Fin (n.len + 1) ↦ f) j :=
  IsOpenImmersion.lift_fac _ _ _

/-- 元の各射影による、同じタプル開から混合積への標準射。 -/
def openFamilyCechFromOpen (n : SimplexCategory) (t : Fin (n.len + 1) → ι) :
    (schemeCechTupleOpen f U (op n) t).toScheme ⟶
      finiteFamilyCechComponent (fun i ↦ (U i).ι ≫ f) n t :=
  WidePullback.lift ((schemeCechTupleOpen f U (op n) t).ι ≫
    WidePullback.base (fun _ : Fin (n.len + 1) ↦ f))
    (openFamilyCechProjection f U n t) (fun j ↦ by
      rw [← Category.assoc, openFamilyCechProjection_fac, Category.assoc,
        WidePullback.π_arrow])

set_option backward.isDefEq.respectTransparency false in
/-- 元の開の混合積は、元の nerve の同じタプル開そのものである。 -/
def openFamilyCechIso (n : SimplexCategory) (t : Fin (n.len + 1) → ι) :
    finiteFamilyCechComponent (fun i ↦ (U i).ι ≫ f) n t ≅
      (schemeCechTupleOpen f U (op n) t).toScheme where
  hom := openFamilyCechToOpen f U n t
  inv := openFamilyCechFromOpen f U n t
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc]
      change openFamilyCechToOpen f U n t ≫
        (WidePullback.lift _ _ _ ≫ WidePullback.π (fun j ↦ (U (t j)).ι ≫ f) j) = _
      rw [WidePullback.lift_π]
      apply (cancel_mono (U (t j)).ι).mp
      rw [Category.assoc, openFamilyCechProjection_fac, ← Category.assoc,
        openFamilyCechToOpen_fac, openFamilyCechInclusion_π, Category.id_comp]
    · rw [Category.assoc]
      change openFamilyCechToOpen f U n t ≫
        (WidePullback.lift _ _ _ ≫ WidePullback.base (fun j ↦ (U (t j)).ι ≫ f)) = _
      rw [WidePullback.lift_base, ← Category.assoc, openFamilyCechToOpen_fac,
        openFamilyCechInclusion_base, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (schemeCechTupleOpen f U (op n) t).ι).mp
    rw [Category.assoc, openFamilyCechToOpen_fac, Category.id_comp]
    apply WidePullback.hom_ext
    · intro j
      change (openFamilyCechFromOpen f U n t ≫ openFamilyCechInclusion f U n t) ≫
        WidePullback.π (fun _ : Fin (n.len + 1) ↦ f) j =
        (schemeCechTupleOpen f U (op n) t).ι ≫ WidePullback.π (fun _ : Fin (n.len + 1) ↦ f) j
      rw [Category.assoc, openFamilyCechInclusion_π, ← Category.assoc]
      change (WidePullback.lift _ _ _ ≫ WidePullback.π (fun j ↦ (U (t j)).ι ≫ f) j) ≫ _ = _
      rw [WidePullback.lift_π, openFamilyCechProjection_fac]
    · change (openFamilyCechFromOpen f U n t ≫ openFamilyCechInclusion f U n t) ≫
        WidePullback.base (fun _ : Fin (n.len + 1) ↦ f) =
        (schemeCechTupleOpen f U (op n) t).ι ≫ WidePullback.base (fun _ : Fin (n.len + 1) ↦ f)
      rw [Category.assoc, openFamilyCechInclusion_base]
      change WidePullback.lift _ _ _ ≫ WidePullback.base (fun j ↦ (U (t j)).ι ≫ f) = _
      rw [WidePullback.lift_base]

/-- 同じ同型と元のタプル開の入射の合成は、元の標準射。 -/
theorem openFamilyCechIso_hom_fac (n : SimplexCategory) (t : Fin (n.len + 1) → ι) :
    (openFamilyCechIso f U n t).hom ≫ (schemeCechTupleOpen f U (op n) t).ι =
      openFamilyCechInclusion f U n t :=
  openFamilyCechToOpen_fac f U n t

set_option backward.isDefEq.respectTransparency false in
/-- 元の標準射は、全ての単体の射による同じ混合積の再添字付けに自然。 -/
theorem openFamilyCechInclusion_naturality {m n : SimplexCategory} (a : m ⟶ n)
    (t : Fin (n.len + 1) → ι) :
    finiteFamilyCechComponentMap (fun i ↦ (U i).ι ≫ f) a t ≫
        openFamilyCechInclusion f U m (fun j ↦ t (a.toOrderHom j)) =
      openFamilyCechInclusion f U n t ≫ (Arrow.mk f).cechNerve.map a.op := by
  apply WidePullback.hom_ext
  · intro j
    change (finiteFamilyCechComponentMap (fun i ↦ (U i).ι ≫ f) a t ≫
      openFamilyCechInclusion f U m (fun j ↦ t (a.toOrderHom j))) ≫
      WidePullback.π (fun _ : Fin (m.len + 1) ↦ f) j =
      (openFamilyCechInclusion f U n t ≫ (Arrow.mk f).cechNerve.map a.op) ≫
      WidePullback.π (fun _ : Fin (m.len + 1) ↦ f) j
    have ha : (Arrow.mk f).cechNerve.map a.op ≫
        WidePullback.π (fun _ : Fin (m.len + 1) ↦ f) j =
      WidePullback.π (fun _ : Fin (n.len + 1) ↦ f) (a.toOrderHom j) := by
      change WidePullback.lift _
        (fun i : Fin (m.len + 1) ↦ WidePullback.π
          (fun _ : Fin (n.len + 1) ↦ f) (a.toOrderHom i)) _ ≫ _ = _
      exact WidePullback.lift_π _ _ _ _ j
    rw [Category.assoc, openFamilyCechInclusion_π, Category.assoc, ha,
      openFamilyCechInclusion_π, ← Category.assoc]
    change (WidePullback.lift _ _ _ ≫ WidePullback.π
      (fun j : Fin (m.len + 1) ↦ (U (t (a.toOrderHom j))).ι ≫ f) j) ≫ _ = _
    rw [WidePullback.lift_π]
  · change (finiteFamilyCechComponentMap (fun i ↦ (U i).ι ≫ f) a t ≫
      openFamilyCechInclusion f U m (fun j ↦ t (a.toOrderHom j))) ≫
      WidePullback.base (fun _ : Fin (m.len + 1) ↦ f) =
      (openFamilyCechInclusion f U n t ≫ (Arrow.mk f).cechNerve.map a.op) ≫
      WidePullback.base (fun _ : Fin (m.len + 1) ↦ f)
    rw [Category.assoc, openFamilyCechInclusion_base, Category.assoc]
    change WidePullback.lift _ _ _ ≫
      WidePullback.base (fun j : Fin (m.len + 1) ↦ (U (t (a.toOrderHom j))).ι ≫ f) =
      openFamilyCechInclusion f U n t ≫
        (WidePullback.lift _ _ _ ≫ WidePullback.base (fun _ : Fin (m.len + 1) ↦ f))
    rw [WidePullback.lift_base, WidePullback.lift_base]
    change WidePullback.base (fun j ↦ (U (t j)).ι ≫ f) =
      openFamilyCechInclusion f U n t ≫ WidePullback.base (fun _ : Fin (n.len + 1) ↦ f)
    exact (openFamilyCechInclusion_base f U n t).symm

set_option backward.isDefEq.respectTransparency false in
/-- 元の nerve の射を、同じタプル開の間に制限する。 -/
def openFamilyCechOpenMap {m n : SimplexCategory} (a : m ⟶ n)
    (t : Fin (n.len + 1) → ι) :
    (schemeCechTupleOpen f U (op n) t).toScheme ⟶
      (schemeCechTupleOpen f U (op m) (fun j ↦ t (a.toOrderHom j))).toScheme :=
  IsOpenImmersion.lift (schemeCechTupleOpen f U (op m) (fun j ↦ t (a.toOrderHom j))).ι
    ((schemeCechTupleOpen f U (op n) t).ι ≫ (Arrow.mk f).cechNerve.map a.op) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact (schemeCechTupleOpen_map_le f U a.op t) x.property)

/-- 同じ制限の射は元の入射と nerve の射に可換。 -/
theorem openFamilyCechOpenMap_fac {m n : SimplexCategory} (a : m ⟶ n)
    (t : Fin (n.len + 1) → ι) :
    openFamilyCechOpenMap f U a t ≫
        (schemeCechTupleOpen f U (op m) (fun j ↦ t (a.toOrderHom j))).ι =
      (schemeCechTupleOpen f U (op n) t).ι ≫ (Arrow.mk f).cechNerve.map a.op :=
  IsOpenImmersion.lift_fac _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- 元の開と混合積の標準同型は、全ての単体の射に自然。 -/
theorem openFamilyCechIso_naturality {m n : SimplexCategory} (a : m ⟶ n)
    (t : Fin (n.len + 1) → ι) :
    finiteFamilyCechComponentMap (fun i ↦ (U i).ι ≫ f) a t ≫
        (openFamilyCechIso f U m (fun j ↦ t (a.toOrderHom j))).hom =
      (openFamilyCechIso f U n t).hom ≫ openFamilyCechOpenMap f U a t := by
  apply (cancel_mono
    (schemeCechTupleOpen f U (op m) (fun j ↦ t (a.toOrderHom j))).ι).mp
  rw [Category.assoc, openFamilyCechIso_hom_fac, Category.assoc,
    openFamilyCechOpenMap_fac, ← Category.assoc, openFamilyCechIso_hom_fac,
    openFamilyCechInclusion_naturality]

end SerrePositivity.AlgebraicGeometry
