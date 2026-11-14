module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.NonpositiveBasis
public import Mathlib.Algebra.Category.ModuleCat.LeftResolution
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.SingleHomology

/-! # 加群の関手的自由解像度

概要：自由加群による自然な全射の核を反復し、非正次数の自由複体を関手的に作る。
方針：Mathlib の LeftResolution を恒等包含に適用し、自然数の鎖複体を整数の余鎖複体へ延長する。
規約：次数 n は余鎖次数 -n。使われ方：離散加群を semifree dg 圏へ送る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits Abelian DifferentialGraded HomologicalComplex
variable (S : Type u) [CommRing S]

/-- 概要：各加群をその元の集合上の自由加群で自然に覆う。
方針：自由・忘却随伴の余単位を LeftResolution の全射に使う。
規約：包含関手は加群圏の恒等関手。使われ方：核を反復する関手的解像度。 -/
def moduleFreeLeftResolution : LeftResolution (𝟭 (ModuleCat.{u} S)) where
  F := forget (ModuleCat.{u} S) ⋙ ModuleCat.free S
  π := (ModuleCat.adj S).counit

/-- 概要：自然な自由被覆の加群は自由である。
方針：元の集合上の有限台関数の基底を使う。
規約：被覆の関手は非加法的でもよい。使われ方：解像度の各段の自由性。 -/
theorem moduleFreeLeftResolution_free (M : ModuleCat.{u} S) :
    Module.Free S ((moduleFreeLeftResolution S).F.obj M) := by
  change Module.Free S (M →₀ S)
  infer_instance

/-- 概要：加群の自然数次数の関手的自由鎖複体。
方針：自然な自由被覆から核を順に解像する標準構成を使う。
規約：微分は次数を一つ下げる。使われ方：整数次数の自由余鎖複体への移送。 -/
abbrev moduleFreeChainResolution : ModuleCat.{u} S ⥤ ChainComplex (ModuleCat.{u} S) ℕ :=
  (moduleFreeLeftResolution S).chainComplexFunctor

/-- 概要：関手的自由鎖複体の各次数は自由加群である。
方針：各次数を自由被覆の像と同定する標準同型を用いる。
規約：基底は選択してよいが射の関手性には選択を使わない。使われ方：semifree 性。 -/
theorem moduleFreeChainResolution_free (M : ModuleCat.{u} S) (n : ℕ) :
    Module.Free S (((moduleFreeChainResolution S).obj M).X n) := by
  let Λ := moduleFreeLeftResolution S
  cases n with
  | zero =>
    exact Module.Free.of_equiv' (moduleFreeLeftResolution_free S M)
      (Λ.chainComplexXZeroIso M).toLinearEquiv.symm
  | succ n =>
    cases n with
    | zero =>
      exact Module.Free.of_equiv' (moduleFreeLeftResolution_free S (kernel (Λ.π.app M)))
        (Λ.chainComplexXOneIso M).toLinearEquiv.symm
    | succ n =>
      exact Module.Free.of_equiv' (moduleFreeLeftResolution_free S
        (kernel (((moduleFreeChainResolution S).obj M).d (n + 1) n)))
        (Λ.chainComplexXIso M n).toLinearEquiv.symm

/-- 概要：自由鎖解像度の次数零から元の加群への自然な全射。
方針：次数零の標準同型と自由被覆の余単位を合成する。
規約：元の加群は次数零に置く。使われ方：増大射。 -/
def moduleFreeChainProjection (M : ModuleCat.{u} S) :
    ((moduleFreeChainResolution S).obj M).X 0 ⟶ M :=
  ((moduleFreeLeftResolution S).chainComplexXZeroIso M).hom ≫
    (moduleFreeLeftResolution S).π.app M

/-- 概要：自由鎖解像度の最初の微分と増大射の合成は零。
方針：最初の微分は核への自由被覆と核の包含を通る。
規約：鎖次数一から零。使われ方：増大鎖写像の構成。 -/
theorem moduleFreeChainProjection_d (M : ModuleCat.{u} S) :
    ((moduleFreeChainResolution S).obj M).d 1 0 ≫ moduleFreeChainProjection S M = 0 := by
  let Λ := moduleFreeLeftResolution S
  have hd := Λ.map_chainComplex_d_1_0 M
  change ((moduleFreeChainResolution S).obj M).d 1 0 = _ at hd
  change ((moduleFreeChainResolution S).obj M).d 1 0 ≫
    (Λ.chainComplexXZeroIso M).hom ≫ Λ.π.app M = 0
  rw [hd]
  simp only [Functor.id_map, Category.assoc, Iso.inv_hom_id_assoc,
    kernel.condition, comp_zero]

/-- 概要：自由鎖複体と元の加群の間の増大鎖写像。
方針：次数零の射を単一複体への鎖写像へ延長する。
規約：元の加群は次数零に集中する。使われ方：解像度の擬同型。 -/
def moduleFreeChainAugmentation (M : ModuleCat.{u} S) :
    (moduleFreeChainResolution S).obj M ⟶ (ChainComplex.single₀ (ModuleCat S)).obj M :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨moduleFreeChainProjection S M, moduleFreeChainProjection_d S M⟩

/-- 概要：自由鎖複体の増大列は次数零で完全である。
方針：微分の核への持ち上げを自由被覆の全射と同定する。
規約：被覆は元の集合上の自由加群。使われ方：増大射の零次ホモロジー同型。 -/
theorem moduleFreeChainProjection_exact (M : ModuleCat.{u} S) :
    (ShortComplex.mk _ _ (moduleFreeChainProjection_d S M)).Exact := by
  let Λ := moduleFreeLeftResolution S
  let L : ShortComplex (ModuleCat S) := ShortComplex.mk
    (Λ.π.app (kernel (Λ.π.app M)) ≫ kernel.ι (Λ.π.app M)) (Λ.π.app M)
      (by simp only [Category.assoc, kernel.condition, comp_zero])
  have hL : L.Exact := by
    rw [ShortComplex.exact_iff_epi_kernel_lift]
    have h : kernel.lift (Λ.π.app M) L.f L.zero = Λ.π.app (kernel (Λ.π.app M)) := by
      apply (cancel_mono (kernel.ι (Λ.π.app M))).1
      rw [kernel.lift_ι]
    rw [h]
    infer_instance
  let e : (ShortComplex.mk _ _ (moduleFreeChainProjection_d S M)) ≅ L :=
    ShortComplex.isoMk (Λ.chainComplexXOneIso M) (Λ.chainComplexXZeroIso M) (Iso.refl M)
      (by
        have hd := Λ.map_chainComplex_d_1_0 M
        change ((moduleFreeChainResolution S).obj M).d 1 0 = _ at hd
        change (Λ.chainComplexXOneIso M).hom ≫
          (Λ.π.app (kernel (Λ.π.app M)) ≫ kernel.ι (Λ.π.app M)) =
            ((moduleFreeChainResolution S).obj M).d 1 0 ≫ (Λ.chainComplexXZeroIso M).hom
        rw [hd]
        simp only [Functor.id_map, Category.assoc, Iso.inv_hom_id, Category.comp_id])
      (by
        change (Λ.chainComplexXZeroIso M).hom ≫ Λ.π.app M = moduleFreeChainProjection S M ≫ 𝟙 M
        rw [Category.comp_id]
        rfl)
  exact (ShortComplex.exact_iff_of_iso e).mpr hL

/-- 概要：自由鎖解像度の次数零の増大射は全射である。
方針：標準同型と自由被覆の全射性を合成する。
規約：圏論的 Epi として与える。使われ方：増大射の余核の普遍性。 -/
instance moduleFreeChainProjection_epi (M : ModuleCat.{u} S) :
    Epi (moduleFreeChainProjection S M) := by
  dsimp only [moduleFreeChainProjection]
  infer_instance

/-- 概要：元の加群は自由鎖解像度の最初の微分の余核である。
方針：増大列の完全性と増大射の全射性を使う。
規約：実際の IsColimit を返す。使われ方：零次ホモロジーの同型。 -/
def moduleFreeChainCokernel (M : ModuleCat.{u} S) :
    IsColimit (CokernelCofork.ofπ (moduleFreeChainProjection S M)
      (moduleFreeChainProjection_d S M)) :=
  (moduleFreeChainProjection_exact S M).gIsCokernel

/-- 概要：自由鎖解像度の零次 opcycles と元の加群の標準同型。
方針：同じ最初の微分の二つの余核を比較する。
規約：同型の前合成は増大射。使われ方：増大射の擬同型性。 -/
def moduleFreeChainOpcyclesIso (M : ModuleCat.{u} S) :
    ((moduleFreeChainResolution S).obj M).opcycles 0 ≅ M :=
  IsColimit.coconePointUniqueUpToIso
    (((moduleFreeChainResolution S).obj M).opcyclesIsCokernel 1 0 (by simp))
    (moduleFreeChainCokernel S M)

/-- 概要：零次 opcycles の比較同型は増大射を因子分解する。
方針：余核の比較同型の脚の公式を使う。
規約：次数零の射として述べる。使われ方：ホモロジー写像の同型性の照合。 -/
theorem moduleFreeChainOpcyclesIso_fac (M : ModuleCat.{u} S) :
    ((moduleFreeChainResolution S).obj M).pOpcycles 0 ≫ (moduleFreeChainOpcyclesIso S M).hom =
      moduleFreeChainProjection S M :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (((moduleFreeChainResolution S).obj M).opcyclesIsCokernel 1 0 (by simp))
    (moduleFreeChainCokernel S M) WalkingParallelPair.one

/-- 概要：自由鎖複体の増大射は擬同型である。
方針：正の鎖次数では核の反復による完全性、零次では余核の比較を使う。
規約：全次数のホモロジーで同型。使われ方：離散加群の導来圏での同定。 -/
theorem moduleFreeChainAugmentation_quasiIso (M : ModuleCat.{u} S) :
    QuasiIso (moduleFreeChainAugmentation S M) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
    have he : opcyclesMap (moduleFreeChainAugmentation S M) 0 =
        (moduleFreeChainOpcyclesIso S M).hom ≫
          (singleObjOpcyclesSelfIso (.down ℕ) 0 M).hom := by
      apply (cancel_epi (((moduleFreeChainResolution S).obj M).pOpcycles 0)).1
      rw [p_opcyclesMap, ← Category.assoc, moduleFreeChainOpcyclesIso_fac]
      rw [show (moduleFreeChainAugmentation S M).f 0 = moduleFreeChainProjection S M from
        ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _]
      rfl
    haveI : IsIso (opcyclesMap (moduleFreeChainAugmentation S M) 0) := by rw [he]; infer_instance
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact IsIso.of_isIso_fac_right (homologyι_naturality (moduleFreeChainAugmentation S M) 0)
  | succ n =>
    apply (quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)).mpr
    exact (moduleFreeLeftResolution S).exactAt_map_chainComplex_succ M n

/-- 概要：自由鎖解像度の増大射は元の加群に関して自然である。
方針：次数零では自由被覆の余単位の自然性、それ以外では終域が零であることを使う。
規約：鎖複体の関手の自然変換。使われ方：離散埋め込みの関手性とホモロジー比較。 -/
def moduleFreeChainAugmentationNat :
    moduleFreeChainResolution S ⟶ ChainComplex.single₀ (ModuleCat S) where
  app := moduleFreeChainAugmentation S
  naturality M N f := by
    apply HomologicalComplex.Hom.ext
    funext n
    cases n with
    | zero =>
      change ((moduleFreeLeftResolution S).chainComplexMap f).f 0 ≫
        (moduleFreeChainAugmentation S N).f 0 =
          (moduleFreeChainAugmentation S M).f 0 ≫ ((ChainComplex.single₀ (ModuleCat S)).map f).f 0
      rw [show (moduleFreeChainAugmentation S N).f 0 = moduleFreeChainProjection S N from
          ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _,
        show (moduleFreeChainAugmentation S M).f 0 = moduleFreeChainProjection S M from
          ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _]
      rw [show ((ChainComplex.single₀ (ModuleCat S)).map f).f 0 = f from rfl]
      simp only [LeftResolution.chainComplexMap_f_0, moduleFreeChainProjection,
        Category.assoc, Iso.inv_hom_id_assoc]
      simpa only [Functor.comp_map, Functor.id_map, Category.assoc]
        using congrArg (fun h => ((moduleFreeLeftResolution S).chainComplexXZeroIso M).hom ≫ h)
          ((moduleFreeLeftResolution S).π.naturality f)
    | succ n =>
      exact (HomologicalComplex.isZero_single_obj_X (.down ℕ) 0 N (n + 1) (by omega)).eq_of_tgt _ _

/-- 概要：加群を非正整数次数の自由複体へ送る関手。
方針：関手的自由鎖複体を n ↦ -n の次数埋め込みで延長する。
規約：正次数は零。使われ方：semifree 解像度の対象と射。 -/
def moduleFreeCochainResolution : ModuleCat.{u} S ⥤ Complex S :=
  moduleFreeChainResolution S ⋙ (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat S))

/-- 概要：自由余鎖解像度の各次数は自由である。
方針：非正次数は鎖複体の自由加群、他の次数は零加群である。
規約：任意の整数次数。使われ方：semibasis の構成。 -/
theorem moduleFreeCochainResolution_free (M : ModuleCat.{u} S) (k : ℤ) :
    Module.Free S (((moduleFreeCochainResolution S).obj M).X k) := by
  let K := (moduleFreeChainResolution S).obj M
  let e := ComplexShape.embeddingDownNat
  by_cases h : ∃ n, e.f n = k
  · obtain ⟨n, hn⟩ := h
    exact Module.Free.of_equiv' (moduleFreeChainResolution_free S M n)
      (K.extendXIso e hn).toLinearEquiv.symm
  · letI : Subsingleton (((moduleFreeCochainResolution S).obj M).X k) :=
      ModuleCat.subsingleton_of_isZero
      (K.isZero_extend_X e k (by simpa only [not_exists] using h))
    infer_instance

/-- 概要：自由余鎖解像度は正次数で零である。
方針：負の自然数は正整数と一致しない。
規約：零対象として述べる。使われ方：高さの厳密下降。 -/
theorem moduleFreeCochainResolution_isZero (M : ModuleCat.{u} S) (k : ℤ) (hk : 0 < k) :
    IsZero (((moduleFreeCochainResolution S).obj M).X k) := by
  apply HomologicalComplex.isZero_extend_X
  intro n
  change -(n : ℤ) ≠ k
  omega

/-- 概要：関手的自由余鎖解像度は既存の意味で semifree である。
方針：次数ごとの自由性と正次数の零性から高さ付き基底を作る。
規約：係数環の条件は可換環のみ。使われ方：Semifree S への関手の持ち上げ。 -/
theorem moduleFreeCochainResolution_semifree (M : ModuleCat.{u} S) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S ((moduleFreeCochainResolution S).obj M) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_of_nonpositive_free _ (moduleFreeCochainResolution_free S M)
    (moduleFreeCochainResolution_isZero S M)

/-- 概要：鎖次数零の加群を余鎖次数零へ移す自然同型。
方針：次数埋め込みに沿う単一複体の標準同型を各加群で取る。
規約：元の加群を変更しない。使われ方：余鎖増大射の自然性。 -/
def moduleSingleExtendIso :
    ChainComplex.single₀ (ModuleCat S) ⋙ ComplexShape.embeddingDownNat.extendFunctor (ModuleCat S) ≅
      HomologicalComplex.single (ModuleCat S) (.up ℤ) 0 :=
  NatIso.ofComponents
    (fun M => HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat M 0 0 rfl)
    (by
      intro M N f
      apply HomologicalComplex.Hom.ext
      funext k
      by_cases hk : k = 0
      · subst hk
        change (HomologicalComplex.extendMap ((ChainComplex.single₀ (ModuleCat S)).map f)
          ComplexShape.embeddingDownNat).f 0 ≫ _ = _ ≫ _
        rw [HomologicalComplex.extendMap_f ((ChainComplex.single₀ (ModuleCat S)).map f)
          ComplexShape.embeddingDownNat (i := 0) (i' := (0 : ℤ)) (by simp)]
        simp only [HomologicalComplex.extendSingleIso_hom_f,
          HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc]
      · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 N k hk).eq_of_tgt _ _)

/-- 概要：関手的自由余鎖解像度の自然な増大射。
方針：鎖増大射を延長し、次数零の単一複体の自然同型と合成する。
規約：元の加群は余鎖次数零。使われ方：離散埋め込みのホモロジー比較。 -/
def moduleFreeCochainAugmentationNat :
    moduleFreeCochainResolution S ⟶ HomologicalComplex.single (ModuleCat S) (.up ℤ) 0 :=
  Functor.whiskerRight (moduleFreeChainAugmentationNat S)
    (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat S)) ≫ (moduleSingleExtendIso S).hom

/-- 概要：自由余鎖解像度から次数零の元の加群への増大射。
方針：自然な増大射を各加群で評価する。
規約：鎖写像として与える。使われ方：ホモロジーの同型。 -/
abbrev moduleFreeCochainAugmentation (M : ModuleCat.{u} S) :
    (moduleFreeCochainResolution S).obj M ⟶
      (HomologicalComplex.single (ModuleCat S) (.up ℤ) 0).obj M :=
  (moduleFreeCochainAugmentationNat S).app M

/-- 概要：関手的自由余鎖解像度の増大射は擬同型である。
方針：鎖増大射の擬同型を次数埋め込みで延長し、単一複体の同型と合成する。
規約：すべての整数次数で成立。使われ方：離散加群の導来圏での同定。 -/
theorem moduleFreeCochainAugmentation_quasiIso (M : ModuleCat.{u} S) :
    QuasiIso (moduleFreeCochainAugmentation S M) := by
  haveI := moduleFreeChainAugmentation_quasiIso S M
  change QuasiIso (HomologicalComplex.extendMap (moduleFreeChainAugmentation S M)
    ComplexShape.embeddingDownNat ≫ (moduleSingleExtendIso S).hom.app M)
  infer_instance

/-- 概要：関手的自由余鎖解像度の零次ホモロジーは元の加群と同型である。
方針：増大射のホモロジー同型と単一複体の標準同型を合成する。
規約：元の加群は S 加群として比較する。使われ方：離散埋め込みの H⁰。 -/
def moduleFreeCochainHomologyZeroIso (M : ModuleCat.{u} S) :
    ((moduleFreeCochainResolution S).obj M).homology 0 ≅ M := by
  haveI := moduleFreeCochainAugmentation_quasiIso S M
  exact isoOfQuasiIsoAt (moduleFreeCochainAugmentation S M) 0 ≪≫
    HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 M

end SerrePositivity.InfinityCategories.Project.DerivedCategories
