module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingFunctor
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeClosedComparison
public import SerrePositivity.KST.SConstruction.DGClosedComparisonPostcomposition
public import SerrePositivity.KST.SConstruction.DGHomGluingInverseRotationProjections

/-!
概要：実 Perf 関手間の全 dg 比較を、二実像小模型の Hom gluing と実逆回転へ接続する。
方針：元二実像と全比較を共通小模型に保持し、既存の厳密 Hom gluing 関手を合成する。
規約：元始域と元全 Hom 比較を保持。使われ方：resolved 商へ延長した実右軸比較の中央射。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  {P : Type w} [DGCategory R P] [Small.{u} P]
  (F G : DGFunctor R P (PerfectDGModule R E))

/-- 概要：元二実関手の全像を同じ和型で指定する。
方針：同じ実対象像を使う。規約：代表を選び直さない。
使われ方：元比較の共通小基底。 -/
def dgPerfectComparisonFamily : P ⊕ P → PerfectDGModule R E := Sum.elim F.obj G.obj

/-- 概要：同じ元二実像を含む共通小模型。
方針：指定二像を小包絡へ入れる。規約：全 Perf の Small 性は仮定しない。
使われ方：元閉比較を保持する恒等 Hom gluing の基底。 -/
abbrev DGPerfectComparisonBase :=
  DGSmallPerfectEnvelope R E (P ⊕ P) (dgPerfectComparisonFamily R E F G)
local notation "T" => DGPerfectComparisonBase R E F G

/-- 概要：元第一関手を同じ共通小模型へ持ち上げる。
方針：指定族の左ラベルと元全 Hom を使う。規約：元対象を保持。
使われ方：元比較の第一成分。 -/
def dgPerfectComparisonFirst : DGFunctor R P (T) :=
  dgSmallPerfectEnvelopeFunctorLift R E (P ⊕ P) (dgPerfectComparisonFamily R E F G)
    F Sum.inl (fun _ => rfl)

/-- 概要：元第二関手を同じ共通小模型へ持ち上げる。
方針：指定族の右ラベルと元全 Hom を使う。規約：元対象を保持。
使われ方：元比較の第二成分。 -/
def dgPerfectComparisonSecond : DGFunctor R P (T) :=
  dgSmallPerfectEnvelopeFunctorLift R E (P ⊕ P) (dgPerfectComparisonFamily R E F G)
    G Sum.inr (fun _ => rfl)

variable (τ : DGFunctorParamTrans R P (PerfectDGModule R E) (𝟙_ (Complex R)) F G)

/-- 概要：元比較を同じ全加群圏の閉射として保持する。
方針：元全 dg 比較を同じ包含で後合成する。
規約：元単位パラメータを保持。使われ方：二実像小模型への比較制限。 -/
def dgPerfectComparisonModuleMap (x : P) :
    ForgetEnrichment.of (Complex R) (F.obj x).val ⟶
      ForgetEnrichment.of (Complex R) (G.obj x).val :=
  ForgetEnrichment.homOf (Complex R) ((dgFunctorParamPost R P
    (PerfectDGModule R E) (RightModule R E) (perfectDGModuleInclusion R E Set.univ) τ).app x)

/-- 概要：元比較の同じ全加群表示は元二関手の全 Hom に関して自然。
方針：元の単位比較の全自然性を回収し、包含の Hom 恒等作用を消去する。
規約：元全次数比較を保持。使われ方：共通小模型の実比較。 -/
lemma dgPerfectComparisonModuleMap_hom_naturality (x y : P) :
    F.map x y ≫ eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) (F.obj x).val) (dgPerfectComparisonModuleMap R E F G τ y) =
    G.map x y ≫ eHomWhiskerRight (Complex R) (dgPerfectComparisonModuleMap R E F G τ x)
      (ForgetEnrichment.of (Complex R) (G.obj y).val) := by
  have h := dgUnitComparison_hom_naturality R
    (F.comp (perfectDGModuleInclusion R E Set.univ))
    (G.comp (perfectDGModuleInclusion R E Set.univ))
    (dgFunctorParamPost R P (PerfectDGModule R E) (RightModule R E)
      (perfectDGModuleInclusion R E Set.univ) τ) x y
  exact (congrArg (fun k => k ≫ eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (F.obj x).val)
      (dgPerfectComparisonModuleMap R E F G τ y)) (Category.comp_id (F.map x y))).symm.trans
    (h.trans (congrArg (fun k => k ≫ eHomWhiskerRight (Complex R)
      (dgPerfectComparisonModuleMap R E F G τ x)
      (ForgetEnrichment.of (Complex R) (G.obj y).val)) (Category.comp_id (G.map x y))))

/-- 概要：元比較を同じ二実像小模型の閉射として保持する。
方針：元全加群の同じ閉射を二段の充満制限へ移す。
規約：元射を保持。使われ方：同じ実 Hom gluing の比較成分。 -/
def dgPerfectComparisonMap (x : P) :
    ForgetEnrichment.of (Complex R) ((dgPerfectComparisonFirst R E F G).obj x) ⟶
      ForgetEnrichment.of (Complex R) ((dgPerfectComparisonSecond R E F G).obj x) :=
  dgSmallPerfectEnvelopeComparisonMap R E (P ⊕ P) (dgPerfectComparisonFamily R E F G)
    F G Sum.inl Sum.inr (fun _ => rfl) (fun _ => rfl)
    (dgPerfectComparisonModuleMap R E F G τ) x

/-- 概要：同じ小模型の元比較は元全 Hom に関して自然。
方針：元全比較の制限を抽象的に適用する。
規約：元全次数を保持。使われ方：同じ厳密 Hom gluing 関手の構成。 -/
lemma dgPerfectComparisonMap_hom_naturality (x y : P) :
    (dgPerfectComparisonFirst R E F G).map x y ≫ eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) ((dgPerfectComparisonFirst R E F G).obj x))
        (dgPerfectComparisonMap R E F G τ y) =
    (dgPerfectComparisonSecond R E F G).map x y ≫ eHomWhiskerRight (Complex R)
        (dgPerfectComparisonMap R E F G τ x)
        (ForgetEnrichment.of (Complex R) ((dgPerfectComparisonSecond R E F G).obj y)) :=
  dgSmallPerfectEnvelopeFunctorLift_comparison_naturality R E (P ⊕ P)
    (dgPerfectComparisonFamily R E F G) F G Sum.inl Sum.inr (fun _ => rfl) (fun _ => rfl)
    (dgPerfectComparisonModuleMap R E F G τ)
    (dgPerfectComparisonModuleMap_hom_naturality R E F G τ) x y

/-- 概要：元全比較を同じ二実像小基底の恒等 Hom gluing へ送る厳密 dg 関手。
方針：元二関手と全自然な閉比較を既存の構成へ渡す。
規約：元始域と元射を保持。使われ方：右軸から恒等への実比較の実 gluing 表示。 -/
def dgPerfectComparisonHomGluingFunctor : DGFunctor R P
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R (T) (T)
      (dgHomGluingBimodule R (T) (T) (T) (DGFunctor.id (T)) (DGFunctor.id (T)))) :=
  dgIdentityHomGluingFunctor R (T) (dgPerfectComparisonFirst R E F G)
    (dgPerfectComparisonSecond R E F G) (dgPerfectComparisonMap R E F G τ)
    (dgPerfectComparisonMap_hom_naturality R E F G τ)

/-- 概要：元比較の実逆回転が用いる同じ小基底。
方針：同じ二実像基底の恒等 Hom gluing の全 cone 像を使う。
規約：元実像を保持。使われ方：LT の実中央比較の終域基底。 -/
abbrev DGPerfectComparisonInverseRotationBase :=
  DGHomGluingLoopConeBase R (T) (T) (T) (DGFunctor.id (T)) (DGFunctor.id (T))
local notation "U" => DGPerfectComparisonInverseRotationBase R E F G

/-- 概要：元全 dg 比較の実逆回転を厳密 dg 関手として保持する。
方針：同じ実 Hom gluing 表示に構成済み実逆回転を合成する。
規約：元始域を変更しない。使われ方：resolved 商上の実中央比較。 -/
def dgPerfectComparisonInverseRotationFunctor : DGFunctor R P
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R (U) (U)
      (dgHomGluingBimodule R (U) (U) (U) (DGFunctor.id (U)) (DGFunctor.id (U)))) :=
  (dgPerfectComparisonHomGluingFunctor R E F G τ).comp
    (dgHomGluingInverseRotationFunctor R (T) (T) (T) (DGFunctor.id (T)) (DGFunctor.id (T)))
/-- 概要：元比較の実逆回転の左射影は同じ実逆 shift cone の合成。
方針：厳密合成の結合則と同じ逆回転の射影回収を使う。
規約：元全 dg 関手の等号。使われ方：実中央射の第一成分。 -/
lemma dgPerfectComparisonInverseRotationFunctor_left :
    (dgPerfectComparisonInverseRotationFunctor R E F G τ).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R (U) (U)
        (dgHomGluingBimodule R (U) (U) (U) (DGFunctor.id (U)) (DGFunctor.id (U)))) =
      (dgPerfectComparisonHomGluingFunctor R E F G τ).comp
        (dgHomGluingLoopConeSmall R (T) (T) (T) (DGFunctor.id (T)) (DGFunctor.id (T))) :=
  (strictDGFunctor_comp_assoc _ _ _).trans
    (congrArg (fun H => (dgPerfectComparisonHomGluingFunctor R E F G τ).comp H)
      (dgHomGluingInverseRotationFunctor_left R (T) (T) (T)
        (DGFunctor.id (T)) (DGFunctor.id (T))))

/-- 概要：元比較の実逆回転の右射影は同じ指定二重 shift 左成分の合成。
方針：厳密合成の結合則と同じ逆回転の射影回収を使う。
規約：元全 dg 関手の等号。使われ方：実中央射の第二成分。 -/
lemma dgPerfectComparisonInverseRotationFunctor_right :
    (dgPerfectComparisonInverseRotationFunctor R E F G τ).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R (U) (U)
        (dgHomGluingBimodule R (U) (U) (U) (DGFunctor.id (U)) (DGFunctor.id (U)))) =
      (dgPerfectComparisonHomGluingFunctor R E F G τ).comp
        (dgHomGluingLoopConeShiftedTarget R (T) (T) (T) (DGFunctor.id (T)) (DGFunctor.id (T))) :=
  (strictDGFunctor_comp_assoc _ _ _).trans
    (congrArg (fun H => (dgPerfectComparisonHomGluingFunctor R E F G τ).comp H)
      (dgHomGluingInverseRotationFunctor_right R (T) (T) (T)
        (DGFunctor.id (T)) (DGFunctor.id (T))))
end SerrePositivity.KST.SConstruction
