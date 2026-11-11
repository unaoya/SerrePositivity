module
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Basic

public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import SerrePositivity.HomotopicalAlgebra.Transfer.Recognition
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.Basic.Countable.Small
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-!
# 非有界コチェイン複体の射影モデル構造

概要：Hovey §2.3、特に定理 2.3.11 の生成射と持ち上げ判定を扱う。
方針：sphere と disk の射を生成元で記述し、境界の持ち上げ判定を再利用する。
規約：`Complex A` は整数次数、微分は +1。モデル構造は局所的に選択する。
使われ方：E∞-dg 代数への右転送の基礎となる複体圏に用いる。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory Limits HomologicalComplex MonoidalCategory
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：Hovey 定義 2.3.3 の生成 cofibration のクラス I。
方針：既存の sphere の境界包含を整数で添字付けする。
規約：コチェイン次数なので `sphere (n+1) → disk n`。
使われ方：射影 cofibration の左持ち上げクラスを生成する。 -/
def projectiveGeneratingCofibrations : MorphismProperty (Complex A) :=
  MorphismProperty.ofHoms (complexSphereToDisk A)

/-- 概要：Hovey 定義 2.3.3 の生成 trivial cofibration のクラス J。
方針：零複体から各 disk への射を用いる。
規約：disk は次数 n と n+1 に集中する。
使われ方：fibration を右持ち上げ性で判定する。 -/
def projectiveGeneratingTrivialCofibrations : MorphismProperty (Complex A) :=
  MorphismProperty.ofHoms
    (fun n : ℤ => (0 : (HomologicalComplex.zero : Complex A) ⟶ complexDisk A n))

/-- 概要：全整数次数で全射な複体射のクラス。
方針：各成分の関数としての全射性を要求する。
規約：基礎環に標数や有限性の仮定を課さない。
使われ方：Hovey 命題 2.3.4 の射影 fibration を表す。 -/
def projectiveFibrations : MorphismProperty (Complex A) :=
  fun _ _ f => ∀ n : ℤ, Function.Surjective (f.f n)

private lemma sphereHom_naturality {K L : Complex A} (n : ℤ)
    (a : complexSphere A n ⟶ K) (f : K ⟶ L) :
    (complexSphereHomEquiv A L n (a ≫ f)).val =
      f.f n (complexSphereHomEquiv A K n a).val := by
  change ((singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).inv ≫
    (a ≫ f).f n) (1 : A) = _
  rw [HomologicalComplex.comp_f]
  rfl

/-- 概要：disk の零包含に対する右持ち上げ性と次数 n の全射性の同値。
方針：disk からの射を次数 n の生成元の像に置き換える。
規約：Hovey 命題 2.3.4 を微分 +1 に翻訳する。
使われ方：J の右持ち上げクラスを同定する。 -/
lemma disk_lifting_iff_surjective {K L : Complex A} (f : K ⟶ L) (n : ℤ) :
    HasLiftingProperty (0 : (HomologicalComplex.zero : Complex A) ⟶ complexDisk A n) f ↔
      Function.Surjective (f.f n) := by
  constructor
  · intro h y
    let b := (complexDiskHomEquiv A L n).symm y
    let sq : CommSq (0 : (HomologicalComplex.zero : Complex A) ⟶ K) 0 f b := ⟨by simp⟩
    obtain ⟨l⟩ := (h.sq_hasLift sq).exists_lift
    refine ⟨complexDiskHomEquiv A K n l.l, ?_⟩
    rw [← complexDiskHomEquiv_naturality, l.fac_right]
    exact (complexDiskHomEquiv A L n).apply_symm_apply y
  · intro h
    constructor
    intro a b sq
    obtain ⟨z, hz⟩ := h (complexDiskHomEquiv A L n b)
    apply CommSq.HasLift.mk'
    refine { l := (complexDiskHomEquiv A K n).symm z
             fac_left := (HomologicalComplex.isZero_zero).eq_of_src _ _
             fac_right := ?_ }
    apply (complexDiskHomEquiv A L n).injective
    rw [complexDiskHomEquiv_naturality, Equiv.apply_symm_apply]
    exact hz

/-- 概要：Hovey 命題 2.3.4、J.rlp は各次数全射のクラス。
方針：各生成 disk について持ち上げ判定を適用する。
規約：射のクラスの等式でありモデル構造を仮定しない。
使われ方：Recognition の hJ に用いる。 -/
lemma projectiveGeneratingTrivialCofibrations_rlp :
    (projectiveGeneratingTrivialCofibrations A).rlp = projectiveFibrations A := by
  ext K L f
  constructor
  · intro h n
    exact (disk_lifting_iff_surjective A f n).1 (h _ (MorphismProperty.ofHoms.mk n))
  · intro h X Y i hi
    cases hi with
    | mk n => exact (disk_lifting_iff_surjective A f n).2 (h n)

/-- 概要：境界包含の右持ち上げ性を生成元の方程式に翻訳する。
方針：sphere の cycle と disk の生成元の像を同時に指定する。
規約：Hovey 命題 2.3.5 の方程式を微分 +1 に翻訳する。
使われ方：I.rlp の擬同型性を既存の cone 判定へ渡す。 -/
lemma sphereToDisk_lifting_iff {K L : Complex A} (f : K ⟶ L) (n : ℤ) :
    HasLiftingProperty (complexSphereToDisk A n) f ↔ complexBoundaryLiftAt A f n := by
  constructor
  · intro h z y hz
    let a := (complexSphereHomEquiv A K (n + 1)).symm z
    let b := (complexDiskHomEquiv A L n).symm y
    have sq : CommSq a (complexSphereToDisk A n) f b := by
      constructor
      apply (complexSphereHomEquiv A L (n + 1)).injective
      apply Subtype.ext
      rw [sphereHom_naturality, complexSphereToDisk_comp]
      simpa only [a, b, Equiv.apply_symm_apply] using hz
    obtain ⟨l⟩ := (h.sq_hasLift sq).exists_lift
    refine ⟨complexDiskHomEquiv A K n l.l, ?_, ?_⟩
    · rw [← complexSphereToDisk_comp, l.fac_left]
      exact congrArg Subtype.val ((complexSphereHomEquiv A K (n + 1)).apply_symm_apply z)
    · rw [← complexDiskHomEquiv_naturality, l.fac_right]
      exact (complexDiskHomEquiv A L n).apply_symm_apply y
  · intro h
    constructor
    intro a b sq
    have hc := congrArg (fun k => (complexSphereHomEquiv A L (n + 1) k).val) sq.w
    rw [sphereHom_naturality, complexSphereToDisk_comp] at hc
    obtain ⟨t, ht, hf⟩ := h (complexSphereHomEquiv A K (n + 1) a)
      (complexDiskHomEquiv A L n b) hc
    apply CommSq.HasLift.mk'
    refine { l := (complexDiskHomEquiv A K n).symm t
             fac_left := ?_
             fac_right := ?_ }
    · apply (complexSphereHomEquiv A K (n + 1)).injective
      apply Subtype.ext
      rw [complexSphereToDisk_comp, Equiv.apply_symm_apply]
      exact ht
    · apply (complexDiskHomEquiv A L n).injective
      rw [complexDiskHomEquiv_naturality, Equiv.apply_symm_apply]
      exact hf

private lemma surjective_of_boundary_lifting {K L : Complex A} (f : K ⟶ L)
    (h : ∀ n : ℤ, complexBoundaryLiftAt A f n) (n : ℤ) : Function.Surjective (f.f n) := by
  intro y
  let y₁ := L.d n (n + 1) y
  have hy₁ : L.d (n + 1) (n + 1 + 1) y₁ = 0 := by
    exact congrArg (fun k => k y) (L.d_comp_d n (n + 1) (n + 1 + 1))
  have hc : f.f (n + 1 + 1) (0 : complexCycles A K (n + 1 + 1)).val =
      L.d (n + 1) (n + 1 + 1) y₁ := by
    rw [hy₁]
    exact map_zero _
  obtain ⟨z, hz, hf⟩ := h (n + 1) 0 y₁ hc
  obtain ⟨t, _, ht⟩ := h n ⟨z, hz⟩ y hf
  exact ⟨t, ht⟩

/-- 概要：Hovey 命題 2.3.5、I.rlp は全射な擬同型のクラス。
方針：境界持ち上げ判定から全射性と cone の非輪状性を導く。
規約：非有界複体に適用し、モデル圏の存在を先取りしない。
使われ方：Recognition の hI に用いる。 -/
lemma projectiveGeneratingCofibrations_rlp :
    (projectiveGeneratingCofibrations A).rlp =
      projectiveFibrations A ⊓ HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ) := by
  ext K L f
  have he : (projectiveGeneratingCofibrations A).rlp f ↔
      ∀ n : ℤ, complexBoundaryLiftAt A f n := by
    constructor
    · intro h n
      exact (sphereToDisk_lifting_iff A f n).1 (h _ (MorphismProperty.ofHoms.mk n))
    · intro h X Y i hi
      cases hi with
      | mk n => exact (sphereToDisk_lifting_iff A f n).2 (h n)
  rw [he]
  constructor
  · intro h
    exact ⟨surjective_of_boundary_lifting A f h, complex_quasiIso_of_boundary_lifting A f h⟩
  · rintro ⟨hs, hq⟩ n
    exact complex_boundary_lifting_of_surjective_quasiIso A f hs hq n

private abbrev degreeUnderlying (n : ℤ) : Complex A ⥤ Type u :=
  HomologicalComplex.eval (ModuleCat A) (.up ℤ) n ⋙ forget (ModuleCat A)

private instance degreeUnderlying_preservesFilteredColimits (n : ℤ) :
    PreservesFilteredColimits (degreeUnderlying A n) := by
  constructor
  intro J _ _
  change PreservesColimitsOfShape J
    (HomologicalComplex.eval (ModuleCat A) (.up ℤ) n ⋙ forget (ModuleCat A))
  infer_instance

attribute [local instance] Cardinal.fact_isRegular_aleph0

private instance complex_hasColimits : HasColimitsOfSize.{u, u} (Complex A) :=
  ⟨fun _ _ => inferInstance⟩

/-- 概要：sphere は有限表示対象である（Hovey 補題 2.3.2）。
方針：生成元を filtered colimit の一段へ持ち上げ、微分零の等式を後の段で実現する。
規約：対象と Hom の宇宙を区別し、小対象引数の宇宙は u とする。
使われ方：I の始域に対する小対象性を証明する。 -/
instance sphere_finitelyPresentable (n : ℤ) :
    IsFinitelyPresentable.{u} (complexSphere A n) := by
  apply IsCardinalPresentable.mk
  intro J _ _ F c hc
  have : IsFiltered J := isFiltered_of_isCardinalFiltered J Cardinal.aleph0
  have hn (i : ℤ) := isColimitOfPreserves (degreeUnderlying A i) hc
  constructor
  · intro g
    let z := complexSphereHomEquiv A c.pt n g
    obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit (hn n) z.val
    have hd : (c.ι.app j).f (n + 1) ((F.obj j).d n (n + 1) x) =
        (c.ι.app j).f (n + 1) 0 := by
      rw [map_zero, ← ModuleCat.comp_apply, ← (c.ι.app j).comm]
      change c.pt.d n (n + 1) ((c.ι.app j).f n x) = 0
      change (c.ι.app j).f n x = z.val at hx
      rw [hx]
      exact z.property
    obtain ⟨k, α, hα⟩ := (Types.FilteredColimit.isColimit_eq_iff' (ht := hn (n + 1)) _ _).1 hd
    change (F.map α).f (n + 1) ((F.obj j).d n (n + 1) x) = (F.map α).f (n + 1) 0 at hα
    have hz : (F.obj k).d n (n + 1) ((F.map α).f n x) = 0 := by
      rw [← ModuleCat.comp_apply, (F.map α).comm]
      simpa using hα
    refine ⟨k, complexSphereMap A n ⟨(F.map α).f n x, hz⟩, ?_⟩
    apply (complexSphereHomEquiv A c.pt n).injective
    apply Subtype.ext
    rw [sphereHom_naturality]
    have he := congrArg Subtype.val
      ((complexSphereHomEquiv A (F.obj k) n).apply_symm_apply ⟨(F.map α).f n x, hz⟩)
    change (complexSphereHomEquiv A (F.obj k) n (complexSphereMap A n _)).val = _ at he
    rw [he]
    change ((F.map α) ≫ c.ι.app k).f n x = _
    rw [c.w α]
    exact hx
  · intro j f₁ f₂ h
    have he := congrArg (fun f => (complexSphereHomEquiv A c.pt n f).val) h
    rw [sphereHom_naturality, sphereHom_naturality] at he
    obtain ⟨k, α, hα⟩ := (Types.FilteredColimit.isColimit_eq_iff' (ht := hn n) _ _).1 he
    refine ⟨k, α, ?_⟩
    apply (complexSphereHomEquiv A (F.obj k) n).injective
    apply Subtype.ext
    rw [sphereHom_naturality, sphereHom_naturality]
    exact hα

/-- 概要：零複体は有限表示対象である（Hovey 補題 2.3.2）。
方針：始域が零の射の一意性と filtered 添字圏の非空性を用いる。
規約：零複体は既存の `HomologicalComplex.zero` を用いる。
使われ方：J の始域に対する小対象性を証明する。 -/
instance zero_finitelyPresentable :
    IsFinitelyPresentable.{u} (HomologicalComplex.zero : Complex A) := by
  apply IsCardinalPresentable.mk
  intro J _ _ F c hc
  have hJ : IsFiltered J := isFiltered_of_isCardinalFiltered J Cardinal.aleph0
  constructor
  · intro g
    exact ⟨hJ.nonempty.some, 0, HomologicalComplex.isZero_zero.eq_of_src _ _⟩
  · intro j f₁ f₂ h
    exact ⟨j, 𝟙 j, HomologicalComplex.isZero_zero.eq_of_src _ _⟩

/-- 概要：I は Mathlib の小対象引数を許す（Hovey 補題 2.3.2）。
方針：整数添字の小さい生成射族と sphere の有限表示性を組み合わせる。
規約：超限反復の補助宇宙は u、正則基数は ℵ₀。
使われ方：Recognition の最初の弱因子分解系を構成する。 -/
instance projectiveGeneratingCofibrations_smallObjectArgument :
    (projectiveGeneratingCofibrations A).HasSmallObjectArgument.{u} := by
  let κ : Cardinal.{u} := Cardinal.aleph0
  let : Fact κ.IsRegular := Cardinal.fact_isRegular_aleph0
  let : Nonempty κ.ord.ToType := Cardinal.nonempty_ord_toType (Fact.out : κ.IsRegular).ne_zero
  let : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot _
  have : (projectiveGeneratingCofibrations A).IsCardinalForSmallObjectArgument κ := by
    refine { isSmall := ?_, preservesColimit := ?_ }
    · change MorphismProperty.IsSmall (MorphismProperty.ofHoms _)
      apply MorphismProperty.isSmall_ofHoms
    · intro K L X Y i hi f hf
      cases hi with
      | mk n =>
        exact preservesColimitsOfShape_of_isCardinalPresentable
          (complexSphere A (n + 1)) κ κ.ord.ToType |>.preservesColimit
  exact ⟨κ, inferInstance, inferInstance, inferInstance⟩

/-- 概要：J は Mathlib の小対象引数を許す（Hovey 補題 2.3.2）。
方針：生成射の始域が有限表示な零複体であることを用いる。
規約：I と同じ補助宇宙 u と正則基数 ℵ₀ を選ぶ。
使われ方：Recognition の第二の弱因子分解系を構成する。 -/
instance projectiveGeneratingTrivialCofibrations_smallObjectArgument :
    (projectiveGeneratingTrivialCofibrations A).HasSmallObjectArgument.{u} := by
  let κ : Cardinal.{u} := Cardinal.aleph0
  let : Fact κ.IsRegular := Cardinal.fact_isRegular_aleph0
  let : Nonempty κ.ord.ToType := Cardinal.nonempty_ord_toType (Fact.out : κ.IsRegular).ne_zero
  let : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot _
  have : (projectiveGeneratingTrivialCofibrations A).IsCardinalForSmallObjectArgument κ := by
    refine { isSmall := ?_, preservesColimit := ?_ }
    · change MorphismProperty.IsSmall (MorphismProperty.ofHoms _)
      apply MorphismProperty.isSmall_ofHoms
    · intro K L X Y i hi f hf
      cases hi with
      | mk n =>
        exact preservesColimitsOfShape_of_isCardinalPresentable
          (HomologicalComplex.zero : Complex A) κ κ.ord.ToType |>.preservesColimit
  exact ⟨κ, inferInstance, inferInstance, inferInstance⟩

private lemma quasiIso_biprod_inl (K L : Complex A) (hL : L.Acyclic) :
    QuasiIso (biprod.inl : K ⟶ K ⊞ L) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := homologyFunctor (ModuleCat A) (.up ℤ) n
  change IsIso (H.map (biprod.inl : K ⟶ K ⊞ L))
  have hz : H.map (biprod.inr : L ⟶ K ⊞ L) = 0 :=
    (hL n).isZero_homology.eq_of_src _ _
  refine ⟨⟨H.map (biprod.fst : K ⊞ L ⟶ K), ?_, ?_⟩⟩
  · rw [← H.map_comp, biprod.inl_fst, H.map_id]
  · have he := congrArg H.map (biprod.total (X := K) (Y := L))
    rw [H.map_add, H.map_comp, H.map_comp, hz, comp_zero, add_zero, H.map_id] at he
    exact he

/-- 概要：J が生成する左持ち上げクラスは擬同型に含まれる（Hovey 命題 2.3.10）。
方針：任意の射を非輪状複体の直和への包含と各次数全射の合成にし、retract を取る。
規約：モデル構造や acyclicity を追加仮定にしない。
使われ方：Recognition の acyclicity 条件を満たす。 -/
lemma projectiveGeneratingTrivialCofibrations_acyclic :
    (projectiveGeneratingTrivialCofibrations A).rlp.llp ≤
      HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ) := by
  intro K L f hf
  let C := CochainComplex.mappingCocone (𝟙 L)
  let p : C ⟶ L := CochainComplex.mappingCocone.fst (𝟙 L)
  have hC : C.Acyclic := SerrePositivity.cochainAcyclic_shift
    ((complex_quasiIso_iff_acyclic_cone A (𝟙 L)).1 inferInstance) (-1)
  let q : K ⊞ C ⟶ L := biprod.desc f p
  have hq : projectiveFibrations A q := by
    intro n y
    let z := (CochainComplex.mappingCocone.inl (𝟙 L)).v n n (add_zero n) y
    refine ⟨(biprod.inr : C ⟶ K ⊞ C).f n z, ?_⟩
    change ((biprod.inr : C ⟶ K ⊞ C) ≫ q).f n z = y
    simp only [q, biprod.inr_desc]
    change ((CochainComplex.mappingCocone.inl (𝟙 L)).v n n (add_zero n) ≫ p.f n) y = y
    rw [CochainComplex.mappingCocone.inl_v_fst_f]
    rfl
  have : HasLiftingProperty f q := hf q (by
    rw [projectiveGeneratingTrivialCofibrations_rlp]
    exact hq)
  have hi : QuasiIso (biprod.inl : K ⟶ K ⊞ C) := quasiIso_biprod_inl A K C hC
  exact quasiIso_of_retractArrow (RetractArrow.ofLeftLiftingProperty
    (show (biprod.inl : K ⟶ K ⊞ C) ≫ q = f by simp [q]))

/-- 概要：射影モデル構造の fibration の選択（Hovey 命題 2.3.4）。
方針：各次数全射のクラスを既存の Mathlib の構造に登録する。
規約：大域 instance にはせず、呼び出し側で局所的に選択する。
使われ方：射影モデル構造の Recognition に用いる。 -/
@[instance_reducible]
def projectiveFibrationStructure : HomotopicalAlgebra.CategoryWithFibrations (Complex A) where
  fibrations := projectiveFibrations A

/-- 概要：射影モデル構造の弱同値の選択（Hovey 定義 2.3.3）。
方針：既存の擬同型のクラスを用いる。
規約：大域 instance に登録しない。
使われ方：E∞-dg 代数の弱同値を底の擬同型で定義する。 -/
@[instance_reducible]
def projectiveWeakEquivalenceStructure :
    HomotopicalAlgebra.CategoryWithWeakEquivalences (Complex A) where
  weakEquivalences := HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ)

/-- 概要：射影 cofibration の選択（Hovey 定義 2.3.3）。
方針：I.rlp に対して左持ち上げ性を持つ射を取る。
規約：各次数の射影性だけで cofibration を定義しない。
使われ方：非有界射影モデル構造の左クラスを与える。 -/
@[instance_reducible]
def projectiveCofibrationStructure : HomotopicalAlgebra.CategoryWithCofibrations (Complex A) where
  cofibrations := (projectiveGeneratingCofibrations A).rlp.llp

/-- 概要：非有界 Ch(A) の射影モデル構造（Hovey 定理 2.3.11）。
方針：両小対象引数、右持ち上げクラスの同定、acyclicity を Recognition に渡す。
規約：`letI := projectiveModelCategory A` として局所利用する。微分は +1。
使われ方：対称オペラッドの代数への右転送のモデル源となる。 -/
@[instance_reducible]
def projectiveModelCategory : HomotopicalAlgebra.ModelCategory (Complex A) := by
  let := projectiveFibrationStructure A
  let := projectiveWeakEquivalenceStructure A
  let := projectiveCofibrationStructure A
  have : (HomotopicalAlgebra.weakEquivalences (Complex A)).HasTwoOutOfThreeProperty :=
    inferInstanceAs (HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ)).HasTwoOutOfThreeProperty
  exact SerrePositivity.ModelGeneration.modelCategoryOfRecognition
    (projectiveGeneratingCofibrations A) (projectiveGeneratingTrivialCofibrations A)
    (projectiveGeneratingCofibrations_rlp A) (projectiveGeneratingTrivialCofibrations_rlp A)
    rfl (projectiveGeneratingTrivialCofibrations_acyclic A)

/-- 概要：構成したモデル構造の弱同値は擬同型に等しい（Hovey 定理 2.3.11）。
方針：Recognition に渡したクラスを展開する。
規約：選択したモデル構造のフィールドを明示する。
使われ方：他のモデル構造の instance と混同せず弱同値を判定する。 -/
lemma projectiveModelCategory_weakEquivalences :
    @HomotopicalAlgebra.weakEquivalences (Complex A) _
      (projectiveModelCategory A).categoryWithWeakEquivalences =
        HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ) := rfl

/-- 概要：構成したモデル構造の fibration は各次数全射（Hovey 定理 2.3.11）。
方針：Recognition に渡したクラスを展開する。
規約：選択したモデル構造のフィールドを明示する。
使われ方：転送モデル構造の底の fibration を判定する。 -/
lemma projectiveModelCategory_fibrations :
    @HomotopicalAlgebra.fibrations (Complex A) _
      (projectiveModelCategory A).categoryWithFibrations = projectiveFibrations A := rfl

/-- 概要：構成したモデル構造は指定した I と J で生成される（Hovey 定理 2.3.11）。
方針：証明済みの小対象性と両右持ち上げクラスの等式を組み合わせる。
規約：モデル構造と小対象引数の宇宙 u を明示する。
使われ方：`Transfer.Right` の `CofibrantlyGenerated` 仮定を満たす。 -/
lemma projectiveModelCategory_cofibrantlyGenerated :
    letI := projectiveModelCategory A
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u}
      (projectiveGeneratingCofibrations A) (projectiveGeneratingTrivialCofibrations A) := by
  let := projectiveModelCategory A
  exact ⟨inferInstance, inferInstance, projectiveGeneratingCofibrations_rlp A,
    projectiveGeneratingTrivialCofibrations_rlp A⟩

end SerrePositivity.EInfinity
