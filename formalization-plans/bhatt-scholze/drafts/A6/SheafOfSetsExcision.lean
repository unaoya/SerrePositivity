-- 将来の置き場所：SerrePositivity.BhattScholze.Perfectoidization.Arc.SheafOfSetsExcision（仮。原典 Cor 8.12 の証明の集合の層の部分）
-- 設計書：formalization-plans/bhatt-scholze/a6-design.md §3.2 の 1〜4、単位 A6-3。基準コミット efa846fe8。型検査対象（5∞-0）。
module
public import SerrePositivity.BhattScholze.Perfectoid.FiniteProduct

public import SerrePositivity.EInfinity.Perfectoidization.TheoryInterface
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BinaryCoproductCocone
-- 本ファイルは drafts/A6/{ArcSite,ArcSheafProperty}.lean、drafts/A5/PerfectSiteComparison.lean を import する。

/-!
# 集合の層の excision（BS 著者版 Cor 8.12 の証明の 1 圏の部分）

## 概要
S → S′ を p 完備環の射、I ⊂ S を p 完備なイデアル、`ArcOutside f I`（I を殺さない V への S → V は S′ → V に一意に延びる）とする。
(1) S → S′ × S/I は arc 被覆。(2) perfd は有限積を保つ（G-A6-2）ので S′ を S′ × S/I に替えてよい。(3) 任意の集合の arc 層 F
（affCompl_κ 上。affPerfd_κ 上の層から `sheafInducedTopologyEquivOfIsCoverDense` で延長したもの）について F(S) = F(S′) ×_{F(S′/I)} F(S/I)。(4) 同値な形：
F_S は集合の層の圏で F_{S′} ⊔_{F_{S′/I}} F_{S/I}（F_T := Hom(T, −)）。

## 方針
(3) は原典の "unraveling"：S → S′ に沿う降下 F(S) = eq(F(S′) ⇉ F(S′ ⊗̂_S S′))、S′ ⊗̂_S S′ → S′ × (S′/I ⊗̂_{S/I} S′/I) が arc 被覆（`ArcOutside` の一意性）
なので F(S′ ⊗̂ S′) ↪ F(S′) × F(S′/I ⊗̂ S′/I)、乗法成分は自明、mod I 成分で x̄ ∈ eq(F(S′/I) ⇉ F(S′/I ⊗̂ S′/I)) = F(S/I)（S/I → S′/I は分裂 arc 被覆）。
すべて Mathlib の 1 圏の層（`Presheaf.IsSheaf`、等化子）。

## 規約
S′ は (2) の後は S′ × S/I。完備テンソルは p 完備。κ は全部の環を含むように取る。

## 使われ方
A6-4（S8 で空間値の層・E 値の層へ持ち上げる）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial

variable (E : SerrePositivity.EInfinity.EInfinityTheory.{u})

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open SerrePositivity.BhattScholze.PerfectoidizationInterface

open SerrePositivity.InfinityCategories SerrePositivity.DerivedCompletion
open SerrePositivity.EInfinity SerrePositivity.EInfinity.Perfectoidization

variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (hR : IsIntegralPerfectoid R p) (κ : Cardinal.{u})

/-! ## (1) 被覆 -/

abbrev ArcSingleton {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :=
  IsArcCoverFamily p (fun _ : PUnit.{u+1} => B) (fun _ => f)

def excisionProduct (U V : A_R R) : A_R R :=
  Under.mk (CommRingCat.ofHom (U.hom.hom.prod V.hom.hom))

def excisionProductMap {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) :
    S ⟶ excisionProduct R T (quotientAlgebra R S I) :=
  Under.homMk (CommRingCat.ofHom (f.right.hom.prod (Ideal.Quotient.mk I))) (by
    sorry) -- f と商射はともに R 上

def outsideTarget {S T : A_R R} (I : Ideal S.right) (i : Bool) : CommRingCat.{u} :=
  if i then T.right else CommRingCat.of (S.right ⧸ I)

def outsideArrow {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) (i : Bool) :
    S.right →+* outsideTarget R (S := S) (T := T) I i := by
  cases i
  · exact Ideal.Quotient.mk I
  · exact f.right.hom

/-- 概要：`ArcOutside f I` なら S → S′ × S/I は arc 被覆（W = V でよい：I ↦ 0 なら S/I を通り、そうでなければ S′ → V に延びる）。
方針：定義の展開。
規約：`IsArcCoverFamily` の二元族 {S → S′, S → S/I}。
使われ方：(3) の降下。 -/
theorem isArcCover_of_arcOutside {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) (h : ArcOutside R p f I) :
    IsArcCoverFamily p (fun i : ULift.{u} Bool => outsideTarget R (S := S) (T := T) I i.down)
      (fun i => outsideArrow R f I i.down) ∧ ArcSingleton p (excisionProductMap R f I).right.hom := by
  sorry -- k が I を殺せば第二射影、そうでなければ h の延長を第一射影に合成。どちらも W=V

/-- 概要：G-A6-9：S → S′ が (1) の形のとき S′ ⊗̂_S S′ → S′ × (S′/I ⊗̂_{S/I} S′/I)（乗法と mod I）は arc 被覆；S/I → S′/I は分裂なので arc 被覆。
方針：S′ ⊗̂_S S′ → V で I ↦ 0 なら第二成分、そうでなければ `ArcOutside` の一意性で二つの S′ → V が一致し乗法を通る。
規約：—
使われ方：(3)。 -/
def arcDiagonalMap {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right)
    (hT : IsModuleComplete T.right (p : T.right) (ModuleCat.of T.right T.right)) :
    let q := (quotientComparison R f I).right
    completionRing p (pushout f.right f.right) →+*
      T.right × completionRing p (pushout q q) := by
  let q := (quotientComparison R f I).right
  let t := (quotientProjection R T (I.map f.right.hom)).right
  let μ : pushout f.right f.right ⟶ T.right := pushout.desc (f := f.right) (g := f.right) (𝟙 T.right) (𝟙 T.right) (by simp)
  let red : pushout f.right f.right ⟶ pushout q q := pushout.desc (f := f.right) (g := f.right) (t ≫ pushout.inl q q) (t ≫ pushout.inr q q) (by
    sorry) -- 商の四角形の可換性と pushout.condition
  exact (_root_.SerrePositivity.BhattScholze.PerfectoidizationInterface.completionLift p μ hT).hom.prod (completionMap p red).hom

theorem isArcCover_diagonal_of_arcOutside {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right)
    (hT : IsModuleComplete T.right (p : T.right) (ModuleCat.of T.right T.right))
    (h : ArcOutside R p f I) : ArcSingleton p (arcDiagonalMap p R f I hT) := by
  sorry -- I を殺す試験射は二つの商の完備テンソルを通る。それ以外は h の一意性で
        -- T からの二脚が一致し、乗法を通る。完備化は試験環への延長を一意に保つ

theorem isArcCover_quotient_split {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) :
    let q := (quotientComparison R (excisionProductMap R f I) I).right
    (∃ r, q ≫ r = 𝟙 _) ∧ ArcSingleton p q.hom ∧ ArcSingleton p (completionMap p q).hom := by
  sorry -- 取り替えた環 T × S/I の第二射影が商でも左逆。完備化で分裂を保つ

/-! ## (2) perfd は有限積を保つ -/

/-- 概要：perfectoid 環 T の冪等元 e について eT は perfectoid；perfectoid 環 T と S′ × S″ → T は T = T′ × T″ に分解し、Perfd_{(S′×S″)/} ≅ Perfd_{S′/} × Perfd_{S″/}。
方針：冪等元の分解、`IsIntegralPerfectoid` の成分ごとの判定。
規約：—
使われ方：`perfectoidization_prod`。 -/
theorem perfectoid_factor_of_idempotent (T : Type u) [CommRing T] (hT : IsIntegralPerfectoid T p)
    (e : T) (he : IsIdempotentElem e) : IsIntegralPerfectoid (T ⧸ Ideal.span {1 - e}) p := by
  sorry -- eT=T/(1−e)。直積分解で完備性・mod p の根・θ の核の生成元を各成分に移す。
        -- 零因子の場合は IsIntegralPerfectoid の Subsingleton 分岐

def productTargets (S T : CommRingCat.{u}) :
    PerfUnder_u p S × PerfUnder_u p T ⥤ PerfUnder_u p (CommRingCat.of (S × T)) where
  obj U := ⟨Under.mk (CommRingCat.ofHom (U.1.obj.hom.hom.prodMap U.2.obj.hom.hom)),
    isIntegralPerfectoid_prod p _ _ U.1.property U.2.property⟩
  map f := ObjectProperty.homMk (Under.homMk
    (CommRingCat.ofHom (f.1.hom.right.hom.prodMap f.2.hom.right.hom)) (by
      sorry)) -- 二つの指定単位の下で可換
  map_id := by sorry -- 各射影で恒等射
  map_comp := by sorry -- 各射影で合成

def perfdUnderProdEquiv (S T : CommRingCat.{u}) :
    PerfUnder_u p (CommRingCat.of (S × T)) ≌ PerfUnder_u p S × PerfUnder_u p T :=
  by
    letI : (productTargets p S T).IsEquivalence := by
      sorry -- (1,0) の像 e と 1−e で分ける。各因子は上の補題で perfectoid、射も成分ごと
    exact (productTargets p S T).asEquivalence.symm

def excisionProdFst (S T : A_R R) : excisionProduct R S T ⟶ S :=
  Under.homMk (CommRingCat.ofHom (RingHom.fst S.right T.right)) (by ext; rfl)

def excisionProdSnd (S T : A_R R) : excisionProduct R S T ⟶ T :=
  Under.homMk (CommRingCat.ofHom (RingHom.snd S.right T.right)) (by ext; rfl)

/-- 二つの環射影を脚とする錐を nerve で取る。 -/
def ringProductCone (S T : A_R R) :
    { c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex S) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex T)) //
      c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (excisionProduct R S T) ∧
      (∀ x : (Δ[0] : SSet.{u+1}) _⦋0⦌,
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c ((coprod.inl : (Δ[0] : SSet.{u+1}) ⟶ Δ[0] ⨿ Δ[0]).app _ x)).edge = (nerve.edgeMk (excisionProdFst R S T)).edge ∧
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg c ((coprod.inr : (Δ[0] : SSet.{u+1}) ⟶ Δ[0] ⨿ Δ[0]).app _ x)).edge = (nerve.edgeMk (excisionProdSnd R S T)).edge) } := by
  sorry -- 二つの射影を二点の左 join に貼り合わせる

/-- 概要：G-A6-2：(S′ × S″)_perfd ≃ S′_perfd × S″_perfd（CAlg_R、D(R)）。
方針：Prop 8.5 の極限の形（A5-1 `perfectoidization_isLimit_u`）と `perfdUnderProdEquiv`：積圏上の (T′, T″) ↦ T′ × T″ の極限は極限の積。
規約：—
使われ方：Cor 8.12 で S′ を S′ × S/I に替えて戻す（D58）。 -/
theorem perfectoidization_prod (S T : A_R R) :
    let c := (ringProductCone R S T).val
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (perfectoidizationFunctor (E := E) p R hR) c) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (e3Perfd (E := E) p R hR) c) := by
  sorry -- Prop 8.5 の κ 版・Type u 版と perfdUnderProdEquiv。両添字圏は零環を終対象にもつ。
        -- 非完備な始域では π₀ の完備化を通す（D41・系4）。忘却はこの積錐を保つ

abbrev quotientExcisionSquare {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) :=
  ordinarySquare R f (quotientProjection R S I) (quotientProjection R T (I.map f.right.hom))
    (quotientComparison R f I) (quotientSquare_commutes R f I)

def excisionPair {A B C : A_R R} (g : A ⟶ B) (h : A ⟶ C) : A ⟶ excisionProduct R B C :=
  Under.homMk (CommRingCat.ofHom (g.right.hom.prod h.right.hom)) (by
    sorry) -- 両成分とも R 上

abbrev excisionCospan {B C D : A_R R} (g : B ⟶ D) (h : C ⟶ D) (F : algebraNerve R ⟶ E.CAlg R) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeCospan (((nerve.edgeMk g).map F).toTruncated) (((nerve.edgeMk h).map F).toTruncated)

def excisionCospanLeg {B C D : A_R R} {g : B ⟶ D} {h : C ⟶ D} {F : algebraNerve R ⟶ E.CAlg R}
    (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (excisionCospan (E := E) R g h F)) (first : Bool) :
    (HomotopyCategory.mk t.vertex : hoFunctor.obj (E.CAlg R)) ⟶
      HomotopyCategory.mk (F.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (if first then B else C))) := by
  let j := if first then horn₂₂.ι₀₂ else horn₂₂.ι₁₂
  let k := j.app _ (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  exact SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg t k) ≫ eqToHom (by
    sorry) -- cospan の第一頂点は B、第二頂点は C

/-- 二つの cospan の極限を、第一・第二射影を保存して比較する。 -/
theorem excisionProductPullback {B C D : A_R R} (g : B ⟶ D) (h : C ⟶ D)
    (F : algebraNerve R ⟶ E.CAlg R)
    (hprod : ∀ U V : A_R R, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone F (ringProductCone R U V).val)) :
    let g' := excisionPair R (excisionProdFst R B C ≫ g) (excisionProdSnd R B C)
    let h' := excisionPair R h (𝟙 C)
    ∀ (t : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (excisionCospan (E := E) R g' h' F)) (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (excisionCospan (E := E) R g h F)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone t → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone v → ∃ e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso t.vertex v.vertex,
        e.hom ≫ excisionCospanLeg (E := E) R v true = excisionCospanLeg (E := E) R t true ≫
          SSet.Truncated.HomotopyCategory.homMk (((nerve.edgeMk (excisionProdFst R B C)).map F).toTruncated) ∧
        e.hom ≫ excisionCospanLeg (E := E) R v false = excisionCospanLeg (E := E) R t false := by
  sorry -- 拡大した錐から B×C の脚を B へ射影する。逆は B と C の脚を対にする。
        -- D×C の第二成分の整合性で両構成は互いに逆

/-- 概要：S″ := S′ × S/I の四角形（S → S″、I）が引き戻しなら、S′ の四角形も引き戻し（S″/IS″ = S′/IS′ × S/I）。
方針（W9-II-19 で訂正）：左上の S_perfd は積に変わらないので「S′ の四角形と恒等四角形の文字どおりの積」ではない。B := S′_perfd、C := (S/I)_perfd、
D := (S′/IS′)_perfd、g : B → D（S′ → S′/IS′ から）、h : C → D（S/I → S′/IS′ から）と書き、`perfectoidization_prod` で S″_perfd ≃ B × C、(S″/IS″)_perfd ≃ D × C。
S″ の四角形の引き戻しは (B × C) ×_{D × C} C（B × C → D × C は (g, id_C)、C → D × C は (h, id_C)）で、有限極限の計算により B ×_D C に標準的に同値、各射影は元の商写像と両立する。結論は変わらない。
規約：—
使われ方：Cor 8.12 の帰着。 -/
theorem excision_of_excision_prod {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right)
    (F : algebraNerve R ⟶ E.CAlg R)
    (hprod : ∀ B C : A_R R, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone F (ringProductCone R B C).val))
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (quotientExcisionSquare R (excisionProductMap R f I) I ≫ F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (quotientExcisionSquare R f I ≫ F) := by
  sorry -- g=F(T→T/IT), h'=F(S/I→T/IT)。商の直積分解と hprod で右・下辺を
        -- (g,id_C) と (h',id_C) に移す。錐の普遍性で (B×C)×_{D×C}C ≃ B×_D C、射影も一致

/-! ## (3)(4) 集合の層の等式 -/

variable [hκ : Fact ((κ + Cardinal.aleph0) ^ Cardinal.aleph0 ≤ κ)]

abbrev PerfdSetSheaf := Sheaf (arcTopologyPerfd p κ) (Type u)
abbrev ComplSetSheaf := Sheaf (arcTopology p κ) (Type u)

def arcSheafEquivalence : PerfdSetSheaf p κ ≌ ComplSetSheaf p κ := by
  let G := (affPerfdInclusion p κ).op
  letI : G.Full := by dsimp [G, affPerfdInclusion]; infer_instance
  letI : G.Faithful := by dsimp [G, affPerfdInclusion]; infer_instance
  letI : G.IsCoverDense (arcTopology p κ) := affPerfdInclusion_isCoverDense p κ
  letI (X : ((AffCompl p κ)ᵒᵖ)ᵒᵖ) : HasLimitsOfShape (StructuredArrow X G.op) (Type u) := inferInstance
  exact G.sheafInducedTopologyEquivOfIsCoverDense (arcTopology p κ) (Type u)

/-- 概要：affPerfd_κ 上の集合の arc 層 F を affCompl_κ へ延長（Mathlib `Functor.sheafInducedTopologyEquivOfIsCoverDense`（`Sites/DenseSubsite/InducedTopology.lean`、
= `Functor.IsDenseSubsite.sheafEquiv`）の .functor（制限の逆）、右 Kan 延長。包含は opposite `affPerfdInclusion.op`、誘導位相 `arcTopologyPerfd`、cover-dense `affPerfdInclusion_isCoverDense`、
値の圏 Set の `HasLimitsOfShape (StructuredArrow X G.op)` を明示。W9-II-25 で名前を訂正）。F(T) = lim_{Perfd_{T/}} F（`Hom(F_T, F) = F(T)` は Kan 延長の随伴）。
方針：`affPerfdInclusion_isCoverDense`（A6-1）。
規約：G-A6-8。
使われ方：以下。 -/
def extendArcSheaf : PerfdSetSheaf p κ ⥤ ComplSetSheaf p κ :=
  (arcSheafEquivalence p κ).functor

def extendArcSheaf_restrict (F : PerfdSetSheaf p κ) :
    (arcSheafEquivalence p κ).inverse.obj ((extendArcSheaf p κ).obj F) ≅ F :=
  ((arcSheafEquivalence p κ).unitIso.app F).symm

def extendArcSheaf_value (F : PerfdSetSheaf p κ) (S : AffCompl p κ) :
    ((extendArcSheaf p κ).obj F).obj.obj (Opposite.op (Opposite.op S)) ≅
      limit (StructuredArrow.proj S (affPerfdInclusion p κ) ⋙ opOp _ ⋙ F.obj) := by
  sorry -- .functor は右 Kan 延長。S→P の comma 圏での点ごとの極限

/-- 完備化した環とその射を同じ small model に送る。 -/
def completedArcObj (U : CommRingCat.{u}) (hU : Cardinal.mk (completionRing p U) ≤ κ) : AffCompl p κ :=
  (equivSmallModel (AffComplLarge p κ)).functor.obj ⟨completionRing p U, completionRing_complete p U, hU⟩

def completedArcMap {U V : CommRingCat.{u}} (f : U ⟶ V)
    (hU : Cardinal.mk (completionRing p U) ≤ κ) (hV : Cardinal.mk (completionRing p V) ≤ κ) :
    completedArcObj p κ U hU ⟶ completedArcObj p κ V hV :=
  (equivSmallModel (AffComplLarge p κ)).functor.map (ObjectProperty.homMk (completionMap p f))

def arcEvalMap (F : ComplSetSheaf p κ) {U V : CommRingCat.{u}} (f : U ⟶ V)
    (hU : Cardinal.mk (completionRing p U) ≤ κ) (hV : Cardinal.mk (completionRing p V) ≤ κ) :=
  F.obj.map ((opOp _).map (completedArcMap p κ f hU hV))

/-- 一つの κ で評価する四隅の上界。T/IT の側も H⁰ 完備化を評価する。 -/
structure ExcisionBounds {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) : Prop where
  source : Cardinal.mk (completionRing p S.right) ≤ κ
  target : Cardinal.mk (completionRing p T.right) ≤ κ
  sourceQuot : Cardinal.mk (completionRing p (quotientAlgebra R S I).right) ≤ κ
  targetQuot : Cardinal.mk (completionRing p (quotientAlgebra R T (I.map f.right.hom)).right) ≤ κ

/-- 概要：(3)：集合の arc 層 F（affCompl_κ 上）、S → S′ が (1) の形なら F(S) ≅ F(S′) ×_{F(S′/I)} F(S/I)。
方針：降下 F(S) = eq(F(S′) ⇉ F(S′ ⊗̂_S S′))、`isArcCover_diagonal_of_arcOutside` で F(S′ ⊗̂ S′) ↪ F(S′) × F(S′/I ⊗̂ S′/I)、成分ごとに読む、
`isArcCover_quotient_split` で eq(F(S′/I) ⇉ F(S′/I ⊗̂ S′/I)) = F(S/I)、分離性で F(S/I) ↪ F(S′/I)。
規約：集合の引き戻し。
使われ方：(4)。 -/
theorem sheafOfSets_excision (F : ComplSetSheaf p κ) {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right)
    (hS : IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right S.right))
    (hT : IsModuleComplete T.right (p : T.right) (ModuleCat.of T.right T.right))
    (hI : IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right I))
    (h : ArcOutside R p f I) (b : ExcisionBounds p R κ f I) :
    IsPullback (arcEvalMap p κ F f.right b.source b.target)
      (arcEvalMap p κ F (quotientProjection R S I).right b.source b.sourceQuot)
      (arcEvalMap p κ F (quotientProjection R T (I.map f.right.hom)).right b.target b.targetQuot)
      (arcEvalMap p κ F (quotientComparison R f I).right b.sourceQuot b.targetQuot) := by
  sorry -- 有限積保存で T×S/I に移る。一点被覆の生成 sieve で相対 Čech 等化子を取り、
        -- 対角被覆の分離性と mod I の分裂で貼る。D1-02 の積条件で元の四角形に戻す

/-- 概要：F_T := Hom(T, −)（affPerfd_κ 上の集合の前層、Prop 8.10 後半で層）。Hom(F_T, F) = F(T)（Yoneda、延長の定義）。
方針：Mathlib の Yoneda と `extendArcSheaf`。
規約：—
使われ方：(4)。 -/
def homSheaf (T : Type u) [CommRing T] : PerfdSetSheaf p κ :=
  ⟨homPresheaf p κ T, (isSheaf_iff_isSheaf_of_type _ _).2 (homPresheaf_isArcSheaf p κ T)⟩

/-- 環の射を前合成する。Hom は全環準同型で、perfectoid 試験環に R 作用を固定しない。 -/
def homSheafMap {U V : CommRingCat.{u}} (f : U ⟶ V) : homSheaf p κ V ⟶ homSheaf p κ U :=
  ObjectProperty.homMk {
    app := fun _ => ↾fun l => l.comp f.hom
    naturality := by intro X Y g; rfl }

def homSheafFunctor : CommRingCat.{u}ᵒᵖ ⥤ PerfdSetSheaf p κ where
  obj X := homSheaf p κ X.unop
  map f := homSheafMap p κ f.unop
  map_id := by sorry -- 環準同型の恒等射との合成
  map_comp := by sorry -- 前合成の結合則

def hom_homSheaf_eq (T : AffCompl p κ) (F : PerfdSetSheaf p κ) :
    (homSheaf p κ ((affComplForget p κ).obj T) ⟶ F) ≃
      ((extendArcSheaf p κ).obj F).obj.obj (Opposite.op (Opposite.op T)) := by
  sorry -- 延長の制限は F、T→P の元ごとの自然な像は extendArcSheaf_value の整合族（Yoneda）

theorem hom_homSheaf_eq_natural {S T : AffCompl p κ} (f : S ⟶ T) (F : PerfdSetSheaf p κ)
    (η : homSheaf p κ ((affComplForget p κ).obj S) ⟶ F) :
    hom_homSheaf_eq p κ T F (homSheafMap p κ ((affComplForget p κ).map f) ≫ η) =
      ((extendArcSheaf p κ).obj F).obj.map ((opOp _).map f) (hom_homSheaf_eq p κ S F η) := by
  sorry -- S の下の整合族を T→P に沿って評価することは f との前合成に一致する

/-- 概要：(4)：F_S は集合の層の圏で押し出し F_{S′} ⊔_{F_{S′/I}} F_{S/I}（(3) と Yoneda）。F_{S′/I} → F_{S′} は単射。
方針：`sheafOfSets_excision`、`hom_homSheaf_eq`。
規約：Mathlib `Sheaf` の押し出し（`presheafToSheaf` の像）。
使われ方：A6-4（S8 で持ち上げ）。 -/
theorem homSheaf_pushout {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right)
    (hS : IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right S.right))
    (hT : IsModuleComplete T.right (p : T.right) (ModuleCat.of T.right T.right))
    (hI : IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right I))
    (h : ArcOutside R p f I) (b : ExcisionBounds p R κ f I) :
    IsPushout (homSheafMap p κ (quotientProjection R T (I.map f.right.hom)).right)
      (homSheafMap p κ (quotientComparison R f I).right)
      (homSheafMap p κ f.right) (homSheafMap p κ (quotientProjection R S I).right) := by
  sorry -- 任意の集合の層 F への Hom を hom_homSheaf_eq で延長の値と同定し、上の引き戻しを適用。
        -- 商から完備な試験環への射は完備化単位を一意に通る
theorem homSheaf_quotient_mono (T : CommRingCat.{u}) (I : Ideal T) :
    Mono (homSheafMap p κ (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
  sorry -- 完備化前の商射は全射なので各 P への前合成は単射。層カテゴリーの mono に移す

end SerrePositivity.BhattScholze.Perfectoidization.Derived
