import SerrePositivity.KST.SConstruction

/-!
概要：S• 構成の公開宣言の型と公理を監査する。
方針：型の検査と公理一覧を各宣言について出力する。
規約：propext・Classical.choice・Quot.sound のみ許可。
使われ方：BGT §7 に対応する保存単位の検証。
-/

#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion
#check @SerrePositivity.KST.SConstruction.arCofiberCompletion
#print axioms SerrePositivity.KST.SConstruction.arCofiberCompletion
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram_boundary
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram_boundary
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.pointFamily
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.pointFamily
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.pointFamily_isCofiber
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.pointFamily_isCofiber
#check @SerrePositivity.KST.SConstruction.arCofiberFamilyOperator
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamilyOperator
#check @SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_vertex
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_vertex
#check @SerrePositivity.KST.SConstruction.IsGapped.arCofiberFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.IsGapped.arCofiberFamily_vertex
#check @SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap
#check @SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_ι
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_ι
#check @SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_apex
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_apex
#check @SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_apex
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_apex
#check @SerrePositivity.KST.SConstruction.intervalStep_mono_endpoints
#print axioms SerrePositivity.KST.SConstruction.intervalStep_mono_endpoints
#check @SerrePositivity.KST.SConstruction.arCofiberSquareOrder
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareOrder
#check @SerrePositivity.KST.SConstruction.arCofiberSquareChain
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareChain
#check @SerrePositivity.KST.SConstruction.arCofiberSquareMap
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareMap
#check @SerrePositivity.KST.SConstruction.arCofiberSquareMap_at
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareMap_at
#check @SerrePositivity.KST.SConstruction.curry_vertex_value
#print axioms SerrePositivity.KST.SConstruction.curry_vertex_value
#check @SerrePositivity.KST.SConstruction.arCofiberFamily
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamily
#check @SerrePositivity.KST.SConstruction.arCofiberFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamily_vertex
#check @SerrePositivity.KST.SConstruction.gappedCofiberFamily
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamily
#check @SerrePositivity.KST.SConstruction.curry_evaluate_vertex
#print axioms SerrePositivity.KST.SConstruction.curry_evaluate_vertex
#check @SerrePositivity.KST.SConstruction.arCofiberSquareMap_apex
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareMap_apex
#check @SerrePositivity.KST.SConstruction.arCofiberFamily_apex
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamily_apex
#check @SerrePositivity.KST.SConstruction.cofiberApex
#print axioms SerrePositivity.KST.SConstruction.cofiberApex
#check @SerrePositivity.KST.SConstruction.gappedCofiberFamily_apex
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamily_apex
#check @SerrePositivity.KST.SConstruction.arCofiberInputOrder
#print axioms SerrePositivity.KST.SConstruction.arCofiberInputOrder
#check @SerrePositivity.KST.SConstruction.arCofiberInputMap
#print axioms SerrePositivity.KST.SConstruction.arCofiberInputMap
#check @SerrePositivity.KST.SConstruction.arCofiberSquareMap_bottom
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareMap_bottom
#check @SerrePositivity.KST.SConstruction.frameCofiberInputOperator
#print axioms SerrePositivity.KST.SConstruction.frameCofiberInputOperator
#check @SerrePositivity.KST.SConstruction.frameCofiberInputs
#print axioms SerrePositivity.KST.SConstruction.frameCofiberInputs
#check @SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_input
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_input
#check @SerrePositivity.KST.SConstruction.gappedFrameRestriction_ι
#print axioms SerrePositivity.KST.SConstruction.gappedFrameRestriction_ι
#check @SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_input
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_input
#check @SerrePositivity.KST.SConstruction.IsCofiberDiagramVertex
#print axioms SerrePositivity.KST.SConstruction.IsCofiberDiagramVertex
#check @SerrePositivity.KST.SConstruction.cofiberDiagrams
#print axioms SerrePositivity.KST.SConstruction.cofiberDiagrams
#check @SerrePositivity.KST.SConstruction.cofiberProjection
#print axioms SerrePositivity.KST.SConstruction.cofiberProjection
#check @SerrePositivity.KST.SConstruction.cofiberForgetZero
#print axioms SerrePositivity.KST.SConstruction.cofiberForgetZero
#check @SerrePositivity.KST.SConstruction.cofiberForgetZero_ι
#print axioms SerrePositivity.KST.SConstruction.cofiberForgetZero_ι
#check @SerrePositivity.KST.SConstruction.cofiberZeroArrow
#print axioms SerrePositivity.KST.SConstruction.cofiberZeroArrow
#check @SerrePositivity.KST.SConstruction.cofiberZeroArrow_ι
#print axioms SerrePositivity.KST.SConstruction.cofiberZeroArrow_ι
#check @SerrePositivity.KST.SConstruction.cofiberZeroArrow_source
#print axioms SerrePositivity.KST.SConstruction.cofiberZeroArrow_source
#check @SerrePositivity.KST.SConstruction.pushoutProjection_bottom
#print axioms SerrePositivity.KST.SConstruction.pushoutProjection_bottom
#check @SerrePositivity.KST.SConstruction.cofiberProjection_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.cofiberProjection_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.exists_relative_cofiberFamily
#print axioms SerrePositivity.KST.SConstruction.exists_relative_cofiberFamily
#check @SerrePositivity.KST.SConstruction.cofiberFamilySpace
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilySpace
#check @SerrePositivity.KST.SConstruction.cofiberFamilySpace_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilySpace_isContractibleKan
#check @SerrePositivity.KST.SConstruction.cofiberFamiliesIso
#print axioms SerrePositivity.KST.SConstruction.cofiberFamiliesIso
#check @SerrePositivity.KST.SConstruction.cofiberSection
#print axioms SerrePositivity.KST.SConstruction.cofiberSection
#check @SerrePositivity.KST.SConstruction.cofiberSection_projection
#print axioms SerrePositivity.KST.SConstruction.cofiberSection_projection
#check @SerrePositivity.KST.SConstruction.cofiberFunctor
#print axioms SerrePositivity.KST.SConstruction.cofiberFunctor
#check @SerrePositivity.KST.SConstruction.arSquare_cofiber_zero_corner
#print axioms SerrePositivity.KST.SConstruction.arSquare_cofiber_zero_corner
#check @SerrePositivity.KST.SConstruction.gappedCofiberTriangle
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberTriangle
#check @SerrePositivity.KST.SConstruction.gappedCofiberTriangle_isCofiber
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberTriangle_isCofiber
#check @SerrePositivity.KST.SConstruction.firstRowNerve
#print axioms SerrePositivity.KST.SConstruction.firstRowNerve
#check @SerrePositivity.KST.SConstruction.firstRowOrder
#print axioms SerrePositivity.KST.SConstruction.firstRowOrder
#check @SerrePositivity.KST.SConstruction.firstRowInclusion
#print axioms SerrePositivity.KST.SConstruction.firstRowInclusion
#check @SerrePositivity.KST.SConstruction.firstRowRestriction
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction
#check @SerrePositivity.KST.SConstruction.gappedDiagram
#print axioms SerrePositivity.KST.SConstruction.gappedDiagram
#check @SerrePositivity.KST.SConstruction.gappedDiagram_isGapped
#print axioms SerrePositivity.KST.SConstruction.gappedDiagram_isGapped
#check @SerrePositivity.KST.SConstruction.firstRowRestriction_vertex
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_vertex
#check @SerrePositivity.KST.SConstruction.firstRowSimplexIso
#print axioms SerrePositivity.KST.SConstruction.firstRowSimplexIso
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData
#check @SerrePositivity.KST.SConstruction.firstRowCofiberData
#print axioms SerrePositivity.KST.SConstruction.firstRowCofiberData
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram_boundary
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram_boundary
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram_isGapped_of_vertexSurjective
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram_isGapped_of_vertexSurjective
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_ι
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_ι
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_boundary
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_boundary
#check @SerrePositivity.KST.SConstruction.boundary_vertex_surjective
#print axioms SerrePositivity.KST.SConstruction.boundary_vertex_surjective
#check @SerrePositivity.KST.SConstruction.exists_gappedBoundaryFilling_of_firstRowFilling
#print axioms SerrePositivity.KST.SConstruction.exists_gappedBoundaryFilling_of_firstRowFilling
#check @SerrePositivity.KST.SConstruction.frame_extend_boundary
#print axioms SerrePositivity.KST.SConstruction.frame_extend_boundary
#check @SerrePositivity.KST.SConstruction.firstRowFrameOrder
#print axioms SerrePositivity.KST.SConstruction.firstRowFrameOrder
#check @SerrePositivity.KST.SConstruction.firstRowFrameMap
#print axioms SerrePositivity.KST.SConstruction.firstRowFrameMap
#check @SerrePositivity.KST.SConstruction.frameRowChain_positive
#print axioms SerrePositivity.KST.SConstruction.frameRowChain_positive
#check @SerrePositivity.KST.SConstruction.frameRowChainInverse
#print axioms SerrePositivity.KST.SConstruction.frameRowChainInverse
#check @SerrePositivity.KST.SConstruction.frameFirstRowMap
#print axioms SerrePositivity.KST.SConstruction.frameFirstRowMap
#check @SerrePositivity.KST.SConstruction.firstRowFrameMap_comp
#print axioms SerrePositivity.KST.SConstruction.firstRowFrameMap_comp
#check @SerrePositivity.KST.SConstruction.frameFirstRowMap_comp
#print axioms SerrePositivity.KST.SConstruction.frameFirstRowMap_comp
#check @SerrePositivity.KST.SConstruction.frameFirstRowIso
#print axioms SerrePositivity.KST.SConstruction.frameFirstRowIso
#check @SerrePositivity.KST.SConstruction.simplexFirstVertex_stdSimplex_of_notMem_boundary
#print axioms SerrePositivity.KST.SConstruction.simplexFirstVertex_stdSimplex_of_notMem_boundary
#check @SerrePositivity.KST.SConstruction.initialBoundaryLifting_ihom_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.initialBoundaryLifting_ihom_of_pointwise
#check @SerrePositivity.KST.SConstruction.isInitialVertex_functorVertex_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.isInitialVertex_functorVertex_of_pointwise
#check @SerrePositivity.KST.SConstruction.isZeroVertex_functorVertex_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.isZeroVertex_functorVertex_of_pointwise
#check @SerrePositivity.KST.SConstruction.isZeroVertex_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.isZeroVertex_of_pointwise
#check @SerrePositivity.KST.SConstruction.evaluateFunctorCocone
#print axioms SerrePositivity.KST.SConstruction.evaluateFunctorCocone
#check @SerrePositivity.KST.SConstruction.IsPointwiseColimitCone
#print axioms SerrePositivity.KST.SConstruction.IsPointwiseColimitCone
#check @SerrePositivity.KST.SConstruction.initialBoundaryLifting_coconeRestriction_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.initialBoundaryLifting_coconeRestriction_of_pointwise
#check @SerrePositivity.KST.SConstruction.isColimitCone_of_pointwise_initialBoundaryLifting
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_of_pointwise_initialBoundaryLifting
#check @SerrePositivity.KST.SConstruction.isColimitCone_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_of_pointwise
#check @SerrePositivity.KST.SConstruction.isPushoutSquare_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.isPushoutSquare_of_pointwise
#check @SerrePositivity.KST.SConstruction.Ar
#print axioms SerrePositivity.KST.SConstruction.Ar
#check @SerrePositivity.KST.SConstruction.arObj
#print axioms SerrePositivity.KST.SConstruction.arObj
#check @SerrePositivity.KST.SConstruction.arMap
#print axioms SerrePositivity.KST.SConstruction.arMap
#check @SerrePositivity.KST.SConstruction.arMap_id
#print axioms SerrePositivity.KST.SConstruction.arMap_id
#check @SerrePositivity.KST.SConstruction.arMap_comp
#print axioms SerrePositivity.KST.SConstruction.arMap_comp
#check @SerrePositivity.KST.SConstruction.arNerve
#print axioms SerrePositivity.KST.SConstruction.arNerve
#check @SerrePositivity.KST.SConstruction.arNerveMap
#print axioms SerrePositivity.KST.SConstruction.arNerveMap
#check @SerrePositivity.KST.SConstruction.arNerveMap_id
#print axioms SerrePositivity.KST.SConstruction.arNerveMap_id
#check @SerrePositivity.KST.SConstruction.arNerveMap_comp
#print axioms SerrePositivity.KST.SConstruction.arNerveMap_comp
#check @SerrePositivity.KST.SConstruction.diagramSpace
#print axioms SerrePositivity.KST.SConstruction.diagramSpace
#check @SerrePositivity.KST.SConstruction.intervalStep
#print axioms SerrePositivity.KST.SConstruction.intervalStep
#check @SerrePositivity.KST.SConstruction.intervalStep_le
#print axioms SerrePositivity.KST.SConstruction.intervalStep_le
#check @SerrePositivity.KST.SConstruction.le_intervalStep
#print axioms SerrePositivity.KST.SConstruction.le_intervalStep
#check @SerrePositivity.KST.SConstruction.arSquareOrder
#print axioms SerrePositivity.KST.SConstruction.arSquareOrder
#check @SerrePositivity.KST.SConstruction.arSquare
#print axioms SerrePositivity.KST.SConstruction.arSquare
#check @SerrePositivity.KST.SConstruction.IsGapped
#print axioms SerrePositivity.KST.SConstruction.IsGapped
#check @SerrePositivity.KST.SConstruction.arSquare_naturality
#print axioms SerrePositivity.KST.SConstruction.arSquare_naturality
#check @SerrePositivity.KST.SConstruction.IsGapped.precomp
#print axioms SerrePositivity.KST.SConstruction.IsGapped.precomp
#check @SerrePositivity.KST.SConstruction.gappedSubcomplex
#print axioms SerrePositivity.KST.SConstruction.gappedSubcomplex
#check @SerrePositivity.KST.SConstruction.sConstruction
#print axioms SerrePositivity.KST.SConstruction.sConstruction
#check @SerrePositivity.KST.SConstruction.sConstruction_quasicategory
#print axioms SerrePositivity.KST.SConstruction.sConstruction_quasicategory
#check @SerrePositivity.KST.SConstruction.sMap
#print axioms SerrePositivity.KST.SConstruction.sMap
#check @SerrePositivity.KST.SConstruction.sMap_ι
#print axioms SerrePositivity.KST.SConstruction.sMap_ι
#check @SerrePositivity.KST.SConstruction.sMap_id
#print axioms SerrePositivity.KST.SConstruction.sMap_id
#check @SerrePositivity.KST.SConstruction.sMap_comp
#print axioms SerrePositivity.KST.SConstruction.sMap_comp
#check @SerrePositivity.KST.SConstruction.simplicialSConstruction
#print axioms SerrePositivity.KST.SConstruction.simplicialSConstruction
#check @SerrePositivity.KST.SConstruction.frameInclusion
#print axioms SerrePositivity.KST.SConstruction.frameInclusion
#check @SerrePositivity.KST.SConstruction.firstRowFrameMap_inclusion
#print axioms SerrePositivity.KST.SConstruction.firstRowFrameMap_inclusion
#check @SerrePositivity.KST.SConstruction.IsGapped.zeroFrameVertex
#print axioms SerrePositivity.KST.SConstruction.IsGapped.zeroFrameVertex
#check @SerrePositivity.KST.SConstruction.gappedFrameRestriction
#print axioms SerrePositivity.KST.SConstruction.gappedFrameRestriction
#check @SerrePositivity.KST.SConstruction.frameRowRestriction
#print axioms SerrePositivity.KST.SConstruction.frameRowRestriction
#check @SerrePositivity.KST.SConstruction.firstRowRestriction_factor
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_factor
#check @SerrePositivity.KST.SConstruction.frameRowDiagramIso
#print axioms SerrePositivity.KST.SConstruction.frameRowDiagramIso
#check @SerrePositivity.KST.SConstruction.frameRowRestriction_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.frameRowRestriction_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.initialBoundaryLifting_map_iso
#print axioms SerrePositivity.KST.SConstruction.initialBoundaryLifting_map_iso
#check @SerrePositivity.KST.SConstruction.internalHomFlipHomEquiv_evaluate
#print axioms SerrePositivity.KST.SConstruction.internalHomFlipHomEquiv_evaluate
#check @SerrePositivity.KST.SConstruction.IsCofiberDiagramVertex.zero_evaluation
#print axioms SerrePositivity.KST.SConstruction.IsCofiberDiagramVertex.zero_evaluation
#check @SerrePositivity.KST.SConstruction.cofiberFamilySquare
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilySquare
#check @SerrePositivity.KST.SConstruction.cofiberFamilySquare_evaluate
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilySquare_evaluate
#check @SerrePositivity.KST.SConstruction.cofiberFamilySquare_zero_corner
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilySquare_zero_corner
#check @SerrePositivity.KST.SConstruction.cofiberFamilyTriangle
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyTriangle
#check @SerrePositivity.KST.SConstruction.cofiberFamilyTriangle_isCofiber
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyTriangle_isCofiber
#check @SerrePositivity.KST.SConstruction.cofiberFamilyTriangle_apex
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyTriangle_apex
#check @SerrePositivity.KST.SConstruction.IsPushoutDiagramVertex
#print axioms SerrePositivity.KST.SConstruction.IsPushoutDiagramVertex
#check @SerrePositivity.KST.SConstruction.pushoutDiagrams
#print axioms SerrePositivity.KST.SConstruction.pushoutDiagrams
#check @SerrePositivity.KST.SConstruction.squareCoconeDiagramIso
#print axioms SerrePositivity.KST.SConstruction.squareCoconeDiagramIso
#check @SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso
#print axioms SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso
#check @SerrePositivity.KST.SConstruction.pushoutProjection
#print axioms SerrePositivity.KST.SConstruction.pushoutProjection
#check @SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso_projection
#print axioms SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso_projection
#check @SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso_inv_projection
#print axioms SerrePositivity.KST.SConstruction.pushoutDiagramsCoconesIso_inv_projection
#check @SerrePositivity.KST.SConstruction.exists_relative_pushoutFamily
#print axioms SerrePositivity.KST.SConstruction.exists_relative_pushoutFamily
#check @SerrePositivity.KST.SConstruction.pushoutProjection_hasLiftingProperty_boundary
#print axioms SerrePositivity.KST.SConstruction.pushoutProjection_hasLiftingProperty_boundary
#check @SerrePositivity.KST.SConstruction.exists_relative_colimitCoconeFamily
#print axioms SerrePositivity.KST.SConstruction.exists_relative_colimitCoconeFamily
#check @SerrePositivity.KST.SConstruction.colimitCoconeFamily_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.colimitCoconeFamily_relative_lifting
#check @SerrePositivity.KST.SConstruction.exists_lift_of_initial_first_vertices
#print axioms SerrePositivity.KST.SConstruction.exists_lift_of_initial_first_vertices
#check @SerrePositivity.KST.SConstruction.exists_extension_with_vertices
#print axioms SerrePositivity.KST.SConstruction.exists_extension_with_vertices
#check @SerrePositivity.KST.SConstruction.exists_extension_of_initial_or_terminal_endpoints
#print axioms SerrePositivity.KST.SConstruction.exists_extension_of_initial_or_terminal_endpoints
#check @SerrePositivity.KST.SConstruction.zeroChoices
#print axioms SerrePositivity.KST.SConstruction.zeroChoices
#check @SerrePositivity.KST.SConstruction.zeroChoices_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.zeroChoices_isContractibleKan
#check @SerrePositivity.KST.SConstruction.zeroChoices_kanComplex
#print axioms SerrePositivity.KST.SConstruction.zeroChoices_kanComplex
#check @SerrePositivity.KST.SConstruction.exists_zeroChoices_extension
#print axioms SerrePositivity.KST.SConstruction.exists_zeroChoices_extension
#check @SerrePositivity.KST.SConstruction.IsDiagonal
#print axioms SerrePositivity.KST.SConstruction.IsDiagonal
#check @SerrePositivity.KST.SConstruction.IsPositiveRow
#print axioms SerrePositivity.KST.SConstruction.IsPositiveRow
#check @SerrePositivity.KST.SConstruction.positiveRow_orderConvex
#print axioms SerrePositivity.KST.SConstruction.positiveRow_orderConvex
#check @SerrePositivity.KST.SConstruction.positiveRow_of_frame_not_diagonal
#print axioms SerrePositivity.KST.SConstruction.positiveRow_of_frame_not_diagonal
#check @SerrePositivity.KST.SConstruction.frameChain_diagonal_endpoint
#print axioms SerrePositivity.KST.SConstruction.frameChain_diagonal_endpoint
#check @SerrePositivity.KST.SConstruction.FrameAr
#print axioms SerrePositivity.KST.SConstruction.FrameAr
#check @SerrePositivity.KST.SConstruction.frameForgetOrder
#print axioms SerrePositivity.KST.SConstruction.frameForgetOrder
#check @SerrePositivity.KST.SConstruction.frameNerve
#print axioms SerrePositivity.KST.SConstruction.frameNerve
#check @SerrePositivity.KST.SConstruction.framePositiveRow
#print axioms SerrePositivity.KST.SConstruction.framePositiveRow
#check @SerrePositivity.KST.SConstruction.frameNerve_diagonal_endpoint
#print axioms SerrePositivity.KST.SConstruction.frameNerve_diagonal_endpoint
#check @SerrePositivity.KST.SConstruction.zeroFrame_extend_boundary
#print axioms SerrePositivity.KST.SConstruction.zeroFrame_extend_boundary
#check @SerrePositivity.KST.SConstruction.IsZeroFrameVertex
#print axioms SerrePositivity.KST.SConstruction.IsZeroFrameVertex
#check @SerrePositivity.KST.SConstruction.zeroFrameDiagrams
#print axioms SerrePositivity.KST.SConstruction.zeroFrameDiagrams
#check @SerrePositivity.KST.SConstruction.zeroFrameProjection
#print axioms SerrePositivity.KST.SConstruction.zeroFrameProjection
#check @SerrePositivity.KST.SConstruction.diagonal_not_positiveRow
#print axioms SerrePositivity.KST.SConstruction.diagonal_not_positiveRow
#check @SerrePositivity.KST.SConstruction.diagonal_not_mem_framePositiveRow
#print axioms SerrePositivity.KST.SConstruction.diagonal_not_mem_framePositiveRow
#check @SerrePositivity.KST.SConstruction.exists_zeroFrame_extension
#print axioms SerrePositivity.KST.SConstruction.exists_zeroFrame_extension
#check @SerrePositivity.KST.SConstruction.zeroFrameProjection_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.zeroFrameProjection_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.mk
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.mk
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.family
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.family
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.boundary
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.boundary
#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.input
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.input
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.mk
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.mk
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.frame
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.frame
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.frame_boundary
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.frame_boundary
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.firstRow
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.firstRow
#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.cofibers
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.cofibers

#check @SerrePositivity.KST.SConstruction.isInitialVertex_pointCoslice_of_isInvertibleEdge
#print axioms SerrePositivity.KST.SConstruction.isInitialVertex_pointCoslice_of_isInvertibleEdge

#check @SerrePositivity.KST.SConstruction.identityCocone
#print axioms SerrePositivity.KST.SConstruction.identityCocone

#check @SerrePositivity.KST.SConstruction.identityCocone_isColimit
#print axioms SerrePositivity.KST.SConstruction.identityCocone_isColimit

#check @SerrePositivity.KST.SConstruction.isColimitCone_iff_of_map_eq
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_iff_of_map_eq

#check @SerrePositivity.KST.SConstruction.identityCocone_val
#print axioms SerrePositivity.KST.SConstruction.identityCocone_val

#check @SerrePositivity.KST.SConstruction.pointCocone_isColimit_of_constant
#print axioms SerrePositivity.KST.SConstruction.pointCocone_isColimit_of_constant

#check @SerrePositivity.KST.SConstruction.horn_one_one_eq_last_face
#print axioms SerrePositivity.KST.SConstruction.horn_one_one_eq_last_face

#check @SerrePositivity.KST.SConstruction.lastVertex_rightAnodyne
#print axioms SerrePositivity.KST.SConstruction.lastVertex_rightAnodyne

#check @SerrePositivity.KST.SConstruction.edgeTargetShape
#print axioms SerrePositivity.KST.SConstruction.edgeTargetShape

#check @SerrePositivity.KST.SConstruction.edgeTargetShape_inl
#print axioms SerrePositivity.KST.SConstruction.edgeTargetShape_inl

#check @SerrePositivity.KST.SConstruction.edgeTargetShape_restrict_last
#print axioms SerrePositivity.KST.SConstruction.edgeTargetShape_restrict_last

#check @SerrePositivity.KST.SConstruction.edgeTargetCocone
#print axioms SerrePositivity.KST.SConstruction.edgeTargetCocone

#check @SerrePositivity.KST.SConstruction.edgeTargetCocone_isColimit
#print axioms SerrePositivity.KST.SConstruction.edgeTargetCocone_isColimit

#check @SerrePositivity.KST.SConstruction.identityLegAttachment_isPushout
#print axioms SerrePositivity.KST.SConstruction.identityLegAttachment_isPushout

#check @SerrePositivity.KST.SConstruction.isColimitCone_iff_restrict_of_identity_leg
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_iff_restrict_of_identity_leg

#check @SerrePositivity.KST.SConstruction.spanCoconeSquare_fst_restrict
#print axioms SerrePositivity.KST.SConstruction.spanCoconeSquare_fst_restrict

#check @SerrePositivity.KST.SConstruction.isPushoutSquare_fst
#print axioms SerrePositivity.KST.SConstruction.isPushoutSquare_fst

#check @SerrePositivity.KST.SConstruction.identityFirstLegAttachment_isPushout
#print axioms SerrePositivity.KST.SConstruction.identityFirstLegAttachment_isPushout

#check @SerrePositivity.KST.SConstruction.isColimitCone_iff_restrict_of_identity_first_leg
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_iff_restrict_of_identity_first_leg

#check @SerrePositivity.KST.SConstruction.spanCoconeSquare_snd_restrict
#print axioms SerrePositivity.KST.SConstruction.spanCoconeSquare_snd_restrict

#check @SerrePositivity.KST.SConstruction.isPushoutSquare_snd
#print axioms SerrePositivity.KST.SConstruction.isPushoutSquare_snd

#check @SerrePositivity.KST.SConstruction.arCofiberSquareOrder_mem_frame
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareOrder_mem_frame

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareOrder
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareOrder

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap_inclusion
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap_inclusion

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareAt
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareAt

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareAt_firstRow
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareAt_firstRow

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareAt_diagonal
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareAt_diagonal

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareAt_isPushout
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareAt_isPushout

#check @SerrePositivity.KST.SConstruction.frameCofiberFamily
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamily

#check @SerrePositivity.KST.SConstruction.frameCofiberFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamily_vertex

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareAt_zero_corner
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareAt_zero_corner

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamily
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamily

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamily_ι
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamily_ι

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap_apex
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap_apex

#check @SerrePositivity.KST.SConstruction.frameCofiberFamily_apex
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamily_apex

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamily_apex
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamily_apex

#check @SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator

#check @SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_vertex
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_vertex

#check @SerrePositivity.KST.SConstruction.IsZeroFrameVertex.frameCofiberFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.IsZeroFrameVertex.frameCofiberFamily_vertex

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_ι
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_ι

#check @SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_apex
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_apex

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_apex
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_apex

#check @SerrePositivity.KST.SConstruction.ihomCurry_pre_whiskerLeft
#print axioms SerrePositivity.KST.SConstruction.ihomCurry_pre_whiskerLeft

#check @SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_frame
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_frame

#check @SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_frame
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_frame

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap_bottom
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap_bottom

#check @SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_input
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_input

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_input
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_input

#check @SerrePositivity.KST.SConstruction.frameInclusion_mono
#print axioms SerrePositivity.KST.SConstruction.frameInclusion_mono

#check @SerrePositivity.KST.SConstruction.exists_arCofiberCompletion_preserving_frame
#print axioms SerrePositivity.KST.SConstruction.exists_arCofiberCompletion_preserving_frame

#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram_frame
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram_frame

#check @SerrePositivity.KST.SConstruction.exists_firstRowCofiberData_preserving_frame
#print axioms SerrePositivity.KST.SConstruction.exists_firstRowCofiberData_preserving_frame

#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_frame
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_frame

#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_firstRow
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.toGapped_firstRow

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_hasLiftingProperty_of_vertexSurjective
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_hasLiftingProperty_of_vertexSurjective

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_hasLiftingProperty_boundary
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_hasLiftingProperty_boundary

#check @SerrePositivity.KST.SConstruction.intervalTriple
#print axioms SerrePositivity.KST.SConstruction.intervalTriple

#check @SerrePositivity.KST.SConstruction.arCofiberRectangleOrder
#print axioms SerrePositivity.KST.SConstruction.arCofiberRectangleOrder

#check @SerrePositivity.KST.SConstruction.arCofiberRectangle
#print axioms SerrePositivity.KST.SConstruction.arCofiberRectangle

#check @SerrePositivity.KST.SConstruction.arCofiberRectangle_left
#print axioms SerrePositivity.KST.SConstruction.arCofiberRectangle_left

#check @SerrePositivity.KST.SConstruction.arCofiberRectangle_outer
#print axioms SerrePositivity.KST.SConstruction.arCofiberRectangle_outer

#check @SerrePositivity.KST.SConstruction.arCofiberRectangle_right
#print axioms SerrePositivity.KST.SConstruction.arCofiberRectangle_right

#check @SerrePositivity.KST.SConstruction.arSquares_isPushout_of_triples
#print axioms SerrePositivity.KST.SConstruction.arSquares_isPushout_of_triples

#check @SerrePositivity.KST.SConstruction.isGapped_iff_triples
#print axioms SerrePositivity.KST.SConstruction.isGapped_iff_triples

#check @SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram_zero_diagonal
#print axioms SerrePositivity.KST.SConstruction.ArCofiberCompletion.diagram_zero_diagonal

#check @SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram_firstRow
#print axioms SerrePositivity.KST.SConstruction.FirstRowCofiberData.diagram_firstRow

#check @SerrePositivity.KST.SConstruction.exists_firstRowDiagramWithZeroDiagonal
#print axioms SerrePositivity.KST.SConstruction.exists_firstRowDiagramWithZeroDiagonal

#check @SerrePositivity.KST.SConstruction.HasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.HasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.exists_pointwiseColimitCone
#print axioms SerrePositivity.KST.SConstruction.exists_pointwiseColimitCone

#check @SerrePositivity.KST.SConstruction.hasColimit_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.hasColimit_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.of_vertexIso
#print axioms SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.of_vertexIso

#check @SerrePositivity.KST.SConstruction.isPointwiseColimitCone_of_isColimitCone_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.isPointwiseColimitCone_of_isColimitCone_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.isColimitCone_iff_pointwise_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_iff_pointwise_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.isPushoutSquare_iff_pointwise_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.isPushoutSquare_iff_pointwise_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.reindexFunctorCocone
#print axioms SerrePositivity.KST.SConstruction.reindexFunctorCocone

#check @SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.reindex
#print axioms SerrePositivity.KST.SConstruction.IsPointwiseColimitCone.reindex

#check @SerrePositivity.KST.SConstruction.isColimitCone_reindex_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_reindex_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.fullSubcomplex_hasLiftingProperty_of_vertexSurjective
#print axioms SerrePositivity.KST.SConstruction.fullSubcomplex_hasLiftingProperty_of_vertexSurjective

#check @SerrePositivity.KST.SConstruction.isInitialVertex_fullSubcomplex_of_ambient
#print axioms SerrePositivity.KST.SConstruction.isInitialVertex_fullSubcomplex_of_ambient

#check @SerrePositivity.KST.SConstruction.isTerminalVertex_fullSubcomplex_of_ambient
#print axioms SerrePositivity.KST.SConstruction.isTerminalVertex_fullSubcomplex_of_ambient

#check @SerrePositivity.KST.SConstruction.isGapped_const
#print axioms SerrePositivity.KST.SConstruction.isGapped_const

#check @SerrePositivity.KST.SConstruction.sConstructionZeroVertex
#print axioms SerrePositivity.KST.SConstruction.sConstructionZeroVertex

#check @SerrePositivity.KST.SConstruction.sConstructionZeroVertex_isZero
#print axioms SerrePositivity.KST.SConstruction.sConstructionZeroVertex_isZero

#check @SerrePositivity.KST.SConstruction.sMap_zeroVertex
#print axioms SerrePositivity.KST.SConstruction.sMap_zeroVertex

#check @SerrePositivity.KST.SConstruction.sConstruction_hasZeroVertex
#print axioms SerrePositivity.KST.SConstruction.sConstruction_hasZeroVertex

#check @SerrePositivity.KST.SConstruction.sConstructionZero_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.sConstructionZero_isZeroVertex

#check @SerrePositivity.KST.SConstruction.sConstructionZero_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.sConstructionZero_isContractibleKan

#check @SerrePositivity.KST.SConstruction.sConstructionZero_kanComplex
#print axioms SerrePositivity.KST.SConstruction.sConstructionZero_kanComplex

#check @SerrePositivity.KST.SConstruction.firstRowZero_hom_ext
#print axioms SerrePositivity.KST.SConstruction.firstRowZero_hom_ext

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_zero_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_zero_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.arSquare_repeat_left
#print axioms SerrePositivity.KST.SConstruction.arSquare_repeat_left

#check @SerrePositivity.KST.SConstruction.arSquare_repeat_right
#print axioms SerrePositivity.KST.SConstruction.arSquare_repeat_right

#check @SerrePositivity.KST.SConstruction.arSquare_isPushout_of_repeated_endpoints
#print axioms SerrePositivity.KST.SConstruction.arSquare_isPushout_of_repeated_endpoints

#check @SerrePositivity.KST.SConstruction.isGapped_one_of_zero_diagonal
#print axioms SerrePositivity.KST.SConstruction.isGapped_one_of_zero_diagonal

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_trivialKanFibration_of_vertexSurjective
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_trivialKanFibration_of_vertexSurjective

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_one_vertex_surjective
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_one_vertex_surjective

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_one_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_one_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.arTwoMiddleSquare
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleSquare

#check @SerrePositivity.KST.SConstruction.arTwoMiddleRetractionOrder
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleRetractionOrder

#check @SerrePositivity.KST.SConstruction.arTwoMiddleRetraction_order_comp
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleRetraction_order_comp

#check @SerrePositivity.KST.SConstruction.arTwoMiddleRetraction
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleRetraction

#check @SerrePositivity.KST.SConstruction.arTwoMiddleSquare_retraction
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleSquare_retraction

#check @SerrePositivity.KST.SConstruction.arTwoMiddleSquare_mono
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleSquare_mono

#check @SerrePositivity.KST.SConstruction.arTwoMiddle
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddle

#check @SerrePositivity.KST.SConstruction.arTwoMiddleIso
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleIso

#check @SerrePositivity.KST.SConstruction.arTwoMiddleIso_ι
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleIso_ι

#check @SerrePositivity.KST.SConstruction.arTwo_obj_middle_or_endpoint
#print axioms SerrePositivity.KST.SConstruction.arTwo_obj_middle_or_endpoint

#check @SerrePositivity.KST.SConstruction.arTwoMiddleRetraction_obj_back
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleRetraction_obj_back

#check @SerrePositivity.KST.SConstruction.arTwoMiddleRetraction_square
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddleRetraction_square

#check @SerrePositivity.KST.SConstruction.arTwoMiddle_mem_of_vertices
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddle_mem_of_vertices

#check @SerrePositivity.KST.SConstruction.arTwoMiddle_vertices_of_mem
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddle_vertices_of_mem

#check @SerrePositivity.KST.SConstruction.arTwoMiddle_notMem_first
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddle_notMem_first

#check @SerrePositivity.KST.SConstruction.arTwoMiddle_notMem_last
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddle_notMem_last

#check @SerrePositivity.KST.SConstruction.arTwoMiddle_missing_endpoint
#print axioms SerrePositivity.KST.SConstruction.arTwoMiddle_missing_endpoint

#check @SerrePositivity.KST.SConstruction.exists_arTwo_extension_with_zero_endpoints
#print axioms SerrePositivity.KST.SConstruction.exists_arTwo_extension_with_zero_endpoints

#check @SerrePositivity.KST.SConstruction.isGapped_two_of_cofiber_middle
#print axioms SerrePositivity.KST.SConstruction.isGapped_two_of_cofiber_middle

#check @SerrePositivity.KST.SConstruction.exists_gapped_arTwo_of_cofiber
#print axioms SerrePositivity.KST.SConstruction.exists_gapped_arTwo_of_cofiber

#check @SerrePositivity.KST.SConstruction.firstRow_two_middle_bottom
#print axioms SerrePositivity.KST.SConstruction.firstRow_two_middle_bottom

#check @SerrePositivity.KST.SConstruction.exists_gapped_arTwo_with_firstRow
#print axioms SerrePositivity.KST.SConstruction.exists_gapped_arTwo_with_firstRow

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_two_vertex_surjective
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_two_vertex_surjective

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_two_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_two_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.relativeCosliceMap_trivialKanFibration_of_initialBoundaryLifting
#print axioms SerrePositivity.KST.SConstruction.relativeCosliceMap_trivialKanFibration_of_initialBoundaryLifting

#check @SerrePositivity.KST.SConstruction.sliceUnder_empty_hom_ext
#print axioms SerrePositivity.KST.SConstruction.sliceUnder_empty_hom_ext

#check @SerrePositivity.KST.SConstruction.cosliceEndpointMap_trivialKanFibration_of_initialBoundaryLifting
#print axioms SerrePositivity.KST.SConstruction.cosliceEndpointMap_trivialKanFibration_of_initialBoundaryLifting

#check @SerrePositivity.KST.SConstruction.exists_relativeInitialCosliceLift
#print axioms SerrePositivity.KST.SConstruction.exists_relativeInitialCosliceLift

#check @SerrePositivity.KST.SConstruction.stdSimplex_firstVertex_leftAnodyne
#print axioms SerrePositivity.KST.SConstruction.stdSimplex_firstVertex_leftAnodyne

#check @SerrePositivity.KST.SConstruction.pointCosliceVertexOfEdge_projection
#print axioms SerrePositivity.KST.SConstruction.pointCosliceVertexOfEdge_projection

#check @SerrePositivity.KST.SConstruction.InitialBoundaryLifting.of_invertibleEdge
#print axioms SerrePositivity.KST.SConstruction.InitialBoundaryLifting.of_invertibleEdge

#check @SerrePositivity.KST.SConstruction.InitialBoundaryLifting.of_vertexIso
#print axioms SerrePositivity.KST.SConstruction.InitialBoundaryLifting.of_vertexIso

#check @SerrePositivity.KST.SConstruction.IsColimitCone.of_functorIso
#print axioms SerrePositivity.KST.SConstruction.IsColimitCone.of_functorIso

#check @SerrePositivity.KST.SConstruction.isColimitCone_iff_of_functorIso
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_iff_of_functorIso

#check @SerrePositivity.KST.SConstruction.IsPushoutSquare.of_functorIso
#print axioms SerrePositivity.KST.SConstruction.IsPushoutSquare.of_functorIso

#check @SerrePositivity.KST.SConstruction.exists_initialCoconeVertex_over_invertible_edge
#print axioms SerrePositivity.KST.SConstruction.exists_initialCoconeVertex_over_invertible_edge

#check @SerrePositivity.KST.SConstruction.HasColimit.of_functorIso
#print axioms SerrePositivity.KST.SConstruction.HasColimit.of_functorIso

#check @SerrePositivity.KST.SConstruction.hasColimit_iff_of_functorIso
#print axioms SerrePositivity.KST.SConstruction.hasColimit_iff_of_functorIso

#check @SerrePositivity.KST.SConstruction.zeroSpanData
#print axioms SerrePositivity.KST.SConstruction.zeroSpanData

#check @SerrePositivity.KST.SConstruction.zeroSpanDataProjection
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDataProjection

#check @SerrePositivity.KST.SConstruction.zeroSpanDataProjection_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDataProjection_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.zeroSpanDataDiagram
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDataDiagram

#check @SerrePositivity.KST.SConstruction.zeroSpanDataDiagram_left
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDataDiagram_left

#check @SerrePositivity.KST.SConstruction.zeroSpanDataDiagram_right
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDataDiagram_right

#check @SerrePositivity.KST.SConstruction.zeroSpan_sources
#print axioms SerrePositivity.KST.SConstruction.zeroSpan_sources

#check @SerrePositivity.KST.SConstruction.zeroSpanDataLift
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDataLift

#check @SerrePositivity.KST.SConstruction.zeroSpanDataLift_projection
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDataLift_projection

#check @SerrePositivity.KST.SConstruction.zeroSpanDataLift_diagram
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDataLift_diagram

#check @SerrePositivity.KST.SConstruction.zeroSpanFamiliesIso
#print axioms SerrePositivity.KST.SConstruction.zeroSpanFamiliesIso

#check @SerrePositivity.KST.SConstruction.zeroSpanDiagramsIso
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDiagramsIso

#check @SerrePositivity.KST.SConstruction.hasColimit_zeroSpan
#print axioms SerrePositivity.KST.SConstruction.hasColimit_zeroSpan

#check @SerrePositivity.KST.SConstruction.cofiberSpan
#print axioms SerrePositivity.KST.SConstruction.cofiberSpan

#check @SerrePositivity.KST.SConstruction.isZeroTargetArrow_pushoutSpan_iff
#print axioms SerrePositivity.KST.SConstruction.isZeroTargetArrow_pushoutSpan_iff

#check @SerrePositivity.KST.SConstruction.zeroSpanFamily_hasColimits
#print axioms SerrePositivity.KST.SConstruction.zeroSpanFamily_hasColimits

#check @SerrePositivity.KST.SConstruction.exists_relative_cofiberFamily_over_span
#print axioms SerrePositivity.KST.SConstruction.exists_relative_cofiberFamily_over_span

#check @SerrePositivity.KST.SConstruction.cofiberSpan_pullback_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.cofiberSpan_pullback_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.cofiberSpan_vertexFiber_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.cofiberSpan_vertexFiber_isContractibleKan

#check @SerrePositivity.KST.SConstruction.IsZeroSpanVertex
#print axioms SerrePositivity.KST.SConstruction.IsZeroSpanVertex

#check @SerrePositivity.KST.SConstruction.zeroSpanDiagrams
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDiagrams

#check @SerrePositivity.KST.SConstruction.zeroSpanDiagrams_quasicategory
#print axioms SerrePositivity.KST.SConstruction.zeroSpanDiagrams_quasicategory

#check @SerrePositivity.KST.SConstruction.cofiberSpanProjection
#print axioms SerrePositivity.KST.SConstruction.cofiberSpanProjection

#check @SerrePositivity.KST.SConstruction.cofiberSpanProjection_ι
#print axioms SerrePositivity.KST.SConstruction.cofiberSpanProjection_ι

#check @SerrePositivity.KST.SConstruction.cofiberSpanProjection_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.cofiberSpanProjection_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.arCofiberZeroInputOrder
#print axioms SerrePositivity.KST.SConstruction.arCofiberZeroInputOrder

#check @SerrePositivity.KST.SConstruction.arCofiberZeroInputMap
#print axioms SerrePositivity.KST.SConstruction.arCofiberZeroInputMap

#check @SerrePositivity.KST.SConstruction.arCofiberInputs_commonSource
#print axioms SerrePositivity.KST.SConstruction.arCofiberInputs_commonSource

#check @SerrePositivity.KST.SConstruction.arCofiberSpan_isPushout
#print axioms SerrePositivity.KST.SConstruction.arCofiberSpan_isPushout

#check @SerrePositivity.KST.SConstruction.arCofiberSpanMap
#print axioms SerrePositivity.KST.SConstruction.arCofiberSpanMap

#check @SerrePositivity.KST.SConstruction.arCofiberSpanMap_left
#print axioms SerrePositivity.KST.SConstruction.arCofiberSpanMap_left

#check @SerrePositivity.KST.SConstruction.arCofiberSpanMap_right
#print axioms SerrePositivity.KST.SConstruction.arCofiberSpanMap_right

#check @SerrePositivity.KST.SConstruction.arCofiberSquareMap_left
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareMap_left

#check @SerrePositivity.KST.SConstruction.arCofiberSquareMap_span
#print axioms SerrePositivity.KST.SConstruction.arCofiberSquareMap_span

#check @SerrePositivity.KST.SConstruction.frameCofiberSpanOperator
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSpanOperator

#check @SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_span
#print axioms SerrePositivity.KST.SConstruction.arCofiberFamilyOperator_span

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap_span
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap_span

#check @SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_span
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamilyOperator_span

#check @SerrePositivity.KST.SConstruction.frameCofiberSpanFamily
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSpanFamily

#check @SerrePositivity.KST.SConstruction.frameCofiberSpanOperator_vertex
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSpanOperator_vertex

#check @SerrePositivity.KST.SConstruction.frameCofiberSpanFamily_zero
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSpanFamily_zero

#check @SerrePositivity.KST.SConstruction.frameCofiberSpans
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSpans

#check @SerrePositivity.KST.SConstruction.frameCofiberSpans_ι
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSpans_ι

#check @SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_span
#print axioms SerrePositivity.KST.SConstruction.gappedCofiberFamiliesMap_span

#check @SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_span
#print axioms SerrePositivity.KST.SConstruction.zeroFrameCofiberFamiliesMap_span

#check @SerrePositivity.KST.SConstruction.exists_arCofiberSpanCompletion_preserving_frame
#print axioms SerrePositivity.KST.SConstruction.exists_arCofiberSpanCompletion_preserving_frame

#check @SerrePositivity.KST.SConstruction.spanTranspose
#print axioms SerrePositivity.KST.SConstruction.spanTranspose

#check @SerrePositivity.KST.SConstruction.spanTranspose_left
#print axioms SerrePositivity.KST.SConstruction.spanTranspose_left

#check @SerrePositivity.KST.SConstruction.spanTranspose_right
#print axioms SerrePositivity.KST.SConstruction.spanTranspose_right

#check @SerrePositivity.KST.SConstruction.spanTranspose_comp_self
#print axioms SerrePositivity.KST.SConstruction.spanTranspose_comp_self

#check @SerrePositivity.KST.SConstruction.spanTransposeIso
#print axioms SerrePositivity.KST.SConstruction.spanTransposeIso

#check @SerrePositivity.KST.SConstruction.spanTranspose_isIso
#print axioms SerrePositivity.KST.SConstruction.spanTranspose_isIso

#check @SerrePositivity.KST.SConstruction.spanTranspose_square
#print axioms SerrePositivity.KST.SConstruction.spanTranspose_square

#check @SerrePositivity.KST.SConstruction.IsPushoutSquare.transpose
#print axioms SerrePositivity.KST.SConstruction.IsPushoutSquare.transpose

#check @SerrePositivity.KST.SConstruction.arVerticalRectangleOrder
#print axioms SerrePositivity.KST.SConstruction.arVerticalRectangleOrder

#check @SerrePositivity.KST.SConstruction.arVerticalRectangle
#print axioms SerrePositivity.KST.SConstruction.arVerticalRectangle

#check @SerrePositivity.KST.SConstruction.arVerticalRectangle_left
#print axioms SerrePositivity.KST.SConstruction.arVerticalRectangle_left

#check @SerrePositivity.KST.SConstruction.arVerticalRectangle_outer
#print axioms SerrePositivity.KST.SConstruction.arVerticalRectangle_outer

#check @SerrePositivity.KST.SConstruction.arVerticalRectangle_right
#print axioms SerrePositivity.KST.SConstruction.arVerticalRectangle_right

#check @SerrePositivity.KST.SConstruction.arTriple_isPushout_of_originSquares
#print axioms SerrePositivity.KST.SConstruction.arTriple_isPushout_of_originSquares

#check @SerrePositivity.KST.SConstruction.isGapped_iff_originSquares
#print axioms SerrePositivity.KST.SConstruction.isGapped_iff_originSquares

#check @SerrePositivity.KST.SConstruction.isGapped_iff_arCofiberFamily_vertices
#print axioms SerrePositivity.KST.SConstruction.isGapped_iff_arCofiberFamily_vertices

#check @SerrePositivity.KST.SConstruction.intervalMaxOrder
#print axioms SerrePositivity.KST.SConstruction.intervalMaxOrder

#check @SerrePositivity.KST.SConstruction.intervalMax
#print axioms SerrePositivity.KST.SConstruction.intervalMax

#check @SerrePositivity.KST.SConstruction.intervalMax_zero
#print axioms SerrePositivity.KST.SConstruction.intervalMax_zero

#check @SerrePositivity.KST.SConstruction.intervalMax_one
#print axioms SerrePositivity.KST.SConstruction.intervalMax_one

#check @SerrePositivity.KST.SConstruction.cofiberUnitCornerPrism
#print axioms SerrePositivity.KST.SConstruction.cofiberUnitCornerPrism

#check @SerrePositivity.KST.SConstruction.arCofiberUnitPrism
#print axioms SerrePositivity.KST.SConstruction.arCofiberUnitPrism

#check @SerrePositivity.KST.SConstruction.cofiberUnitCorner
#print axioms SerrePositivity.KST.SConstruction.cofiberUnitCorner

#check @SerrePositivity.KST.SConstruction.cofiberUnitCornerPrism_zero
#print axioms SerrePositivity.KST.SConstruction.cofiberUnitCornerPrism_zero

#check @SerrePositivity.KST.SConstruction.cofiberUnitCornerPrism_one
#print axioms SerrePositivity.KST.SConstruction.cofiberUnitCornerPrism_one

#check @SerrePositivity.KST.SConstruction.arCofiberUnitSquare
#print axioms SerrePositivity.KST.SConstruction.arCofiberUnitSquare

#check @SerrePositivity.KST.SConstruction.arCofiberUnitPrism_zero
#print axioms SerrePositivity.KST.SConstruction.arCofiberUnitPrism_zero

#check @SerrePositivity.KST.SConstruction.arCofiberUnitPrism_one
#print axioms SerrePositivity.KST.SConstruction.arCofiberUnitPrism_one

#check @SerrePositivity.KST.SConstruction.arCofiberUnitPrism_lower
#print axioms SerrePositivity.KST.SConstruction.arCofiberUnitPrism_lower

#check @SerrePositivity.KST.SConstruction.arCofiberUnitPrism_upper
#print axioms SerrePositivity.KST.SConstruction.arCofiberUnitPrism_upper

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap_row_right
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap_row_right

#check @SerrePositivity.KST.SConstruction.arCofiberUnitPrism_vertex_constant
#print axioms SerrePositivity.KST.SConstruction.arCofiberUnitPrism_vertex_constant

#check @SerrePositivity.KST.SConstruction.arCofiberUnitComparisonIso
#print axioms SerrePositivity.KST.SConstruction.arCofiberUnitComparisonIso

#check @SerrePositivity.KST.SConstruction.arSquareFamilyDiagram
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyDiagram

#check @SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_evaluate
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_evaluate

#check @SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_frame
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_frame

#check @SerrePositivity.KST.SConstruction.arSquareFamilyUnitComparisonIso
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyUnitComparisonIso

#check @SerrePositivity.KST.SConstruction.cofiberFamilyUnitComparisonIso
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyUnitComparisonIso

#check @SerrePositivity.KST.SConstruction.squareHorizontalPrism
#print axioms SerrePositivity.KST.SConstruction.squareHorizontalPrism

#check @SerrePositivity.KST.SConstruction.squareVerticalPrism
#print axioms SerrePositivity.KST.SConstruction.squareVerticalPrism

#check @SerrePositivity.KST.SConstruction.cofiberTopCorner
#print axioms SerrePositivity.KST.SConstruction.cofiberTopCorner

#check @SerrePositivity.KST.SConstruction.squareHorizontalPrism_zero
#print axioms SerrePositivity.KST.SConstruction.squareHorizontalPrism_zero

#check @SerrePositivity.KST.SConstruction.squareHorizontalPrism_one
#print axioms SerrePositivity.KST.SConstruction.squareHorizontalPrism_one

#check @SerrePositivity.KST.SConstruction.squareVerticalPrism_zero
#print axioms SerrePositivity.KST.SConstruction.squareVerticalPrism_zero

#check @SerrePositivity.KST.SConstruction.squareVerticalPrism_one
#print axioms SerrePositivity.KST.SConstruction.squareVerticalPrism_one

#check @SerrePositivity.KST.SConstruction.arFixedStartSquare
#print axioms SerrePositivity.KST.SConstruction.arFixedStartSquare

#check @SerrePositivity.KST.SConstruction.arCofiberComparisonSquare
#print axioms SerrePositivity.KST.SConstruction.arCofiberComparisonSquare

#check @SerrePositivity.KST.SConstruction.arCofiberComparisonUnitSquare
#print axioms SerrePositivity.KST.SConstruction.arCofiberComparisonUnitSquare

#check @SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism
#print axioms SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism

#check @SerrePositivity.KST.SConstruction.arCofiberTargetPrism
#print axioms SerrePositivity.KST.SConstruction.arCofiberTargetPrism

#check @SerrePositivity.KST.SConstruction.arCofiberSourcePrism
#print axioms SerrePositivity.KST.SConstruction.arCofiberSourcePrism

#check @SerrePositivity.KST.SConstruction.arFixedStartSquare_unitCorner
#print axioms SerrePositivity.KST.SConstruction.arFixedStartSquare_unitCorner

#check @SerrePositivity.KST.SConstruction.arSquare_topCorner
#print axioms SerrePositivity.KST.SConstruction.arSquare_topCorner

#check @SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_zero
#print axioms SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_zero

#check @SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_one
#print axioms SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_one

#check @SerrePositivity.KST.SConstruction.arCofiberTargetPrism_zero
#print axioms SerrePositivity.KST.SConstruction.arCofiberTargetPrism_zero

#check @SerrePositivity.KST.SConstruction.arCofiberTargetPrism_one
#print axioms SerrePositivity.KST.SConstruction.arCofiberTargetPrism_one

#check @SerrePositivity.KST.SConstruction.arCofiberSourcePrism_zero
#print axioms SerrePositivity.KST.SConstruction.arCofiberSourcePrism_zero

#check @SerrePositivity.KST.SConstruction.arCofiberSourcePrism_one
#print axioms SerrePositivity.KST.SConstruction.arCofiberSourcePrism_one

#check @SerrePositivity.KST.SConstruction.squareVertexLine
#print axioms SerrePositivity.KST.SConstruction.squareVertexLine

#check @SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_left
#print axioms SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_left

#check @SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_right
#print axioms SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_right

#check @SerrePositivity.KST.SConstruction.arCofiberTargetPrism_left
#print axioms SerrePositivity.KST.SConstruction.arCofiberTargetPrism_left

#check @SerrePositivity.KST.SConstruction.arCofiberTargetPrism_right
#print axioms SerrePositivity.KST.SConstruction.arCofiberTargetPrism_right

#check @SerrePositivity.KST.SConstruction.arCofiberSourcePrism_lower
#print axioms SerrePositivity.KST.SConstruction.arCofiberSourcePrism_lower

#check @SerrePositivity.KST.SConstruction.arCofiberSourcePrism_upper
#print axioms SerrePositivity.KST.SConstruction.arCofiberSourcePrism_upper

#check @SerrePositivity.KST.SConstruction.frameCofiberSquareMap_diagonal_horizontal
#print axioms SerrePositivity.KST.SConstruction.frameCofiberSquareMap_diagonal_horizontal

#check @SerrePositivity.KST.SConstruction.arCofiberZeroInputMap_fixedStart
#print axioms SerrePositivity.KST.SConstruction.arCofiberZeroInputMap_fixedStart

#check @SerrePositivity.KST.SConstruction.arCofiberInputMap_fixedTarget
#print axioms SerrePositivity.KST.SConstruction.arCofiberInputMap_fixedTarget

#check @SerrePositivity.KST.SConstruction.functorIsoOfSquareConstantPrism
#print axioms SerrePositivity.KST.SConstruction.functorIsoOfSquareConstantPrism

#check @SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_constant
#print axioms SerrePositivity.KST.SConstruction.arCofiberHorizontalPrism_constant

#check @SerrePositivity.KST.SConstruction.arCofiberTargetPrism_constant
#print axioms SerrePositivity.KST.SConstruction.arCofiberTargetPrism_constant

#check @SerrePositivity.KST.SConstruction.arCofiberSourcePrism_constant
#print axioms SerrePositivity.KST.SConstruction.arCofiberSourcePrism_constant

#check @SerrePositivity.KST.SConstruction.arCofiberHorizontalComparisonIso
#print axioms SerrePositivity.KST.SConstruction.arCofiberHorizontalComparisonIso

#check @SerrePositivity.KST.SConstruction.arCofiberTargetComparisonIso
#print axioms SerrePositivity.KST.SConstruction.arCofiberTargetComparisonIso

#check @SerrePositivity.KST.SConstruction.arCofiberSourceComparisonIso
#print axioms SerrePositivity.KST.SConstruction.arCofiberSourceComparisonIso

#check @SerrePositivity.KST.SConstruction.arCofiberSelectedSquareComparisonIso
#print axioms SerrePositivity.KST.SConstruction.arCofiberSelectedSquareComparisonIso

#check @SerrePositivity.KST.SConstruction.arCofiberCanonicalSquareComparisonIso
#print axioms SerrePositivity.KST.SConstruction.arCofiberCanonicalSquareComparisonIso

#check @SerrePositivity.KST.SConstruction.arSquareFamilyApex
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyApex

#check @SerrePositivity.KST.SConstruction.arSquareFamilyApex_frame
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyApex_frame

#check @SerrePositivity.KST.SConstruction.isGapped_arSquareFamilyApex
#print axioms SerrePositivity.KST.SConstruction.isGapped_arSquareFamilyApex

#check @SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_span
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_span

#check @SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_left
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_left

#check @SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_bottom
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_bottom

#check @SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_at
#print axioms SerrePositivity.KST.SConstruction.arSquareFamilyDiagram_at

#check @SerrePositivity.KST.SConstruction.isGapped_cofiberFamily_of_fixed_span
#print axioms SerrePositivity.KST.SConstruction.isGapped_cofiberFamily_of_fixed_span

#check @SerrePositivity.KST.SConstruction.frameCofiberFamily_span
#print axioms SerrePositivity.KST.SConstruction.frameCofiberFamily_span

#check @SerrePositivity.KST.SConstruction.exists_cofiberFamily_of_zeroFrame
#print axioms SerrePositivity.KST.SConstruction.exists_cofiberFamily_of_zeroFrame

#check @SerrePositivity.KST.SConstruction.exists_gapped_extension_of_zeroFrame
#print axioms SerrePositivity.KST.SConstruction.exists_gapped_extension_of_zeroFrame

#check @SerrePositivity.KST.SConstruction.zeroFrameVertex_of_zero_diagonal
#print axioms SerrePositivity.KST.SConstruction.zeroFrameVertex_of_zero_diagonal

#check @SerrePositivity.KST.SConstruction.exists_gapped_with_firstRow
#print axioms SerrePositivity.KST.SConstruction.exists_gapped_with_firstRow

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_vertex_surjective
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_vertex_surjective

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_vertexFiber_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_vertexFiber_isContractibleKan

#check @SerrePositivity.KST.SConstruction.firstRowEquivalence
#print axioms SerrePositivity.KST.SConstruction.firstRowEquivalence

#check @SerrePositivity.KST.SConstruction.coreSConstruction
#print axioms SerrePositivity.KST.SConstruction.coreSConstruction

#check @SerrePositivity.KST.SConstruction.coreSConstruction_kanComplex
#print axioms SerrePositivity.KST.SConstruction.coreSConstruction_kanComplex

#check @SerrePositivity.KST.SConstruction.coreSMap
#print axioms SerrePositivity.KST.SConstruction.coreSMap

#check @SerrePositivity.KST.SConstruction.simplicialCoreSConstruction
#print axioms SerrePositivity.KST.SConstruction.simplicialCoreSConstruction

#check @SerrePositivity.KST.SConstruction.simplicialCoreSConstruction_obj_kanComplex
#print axioms SerrePositivity.KST.SConstruction.simplicialCoreSConstruction_obj_kanComplex

#check @SerrePositivity.KST.SConstruction.coreSConstructionZeroVertex
#print axioms SerrePositivity.KST.SConstruction.coreSConstructionZeroVertex

#check @SerrePositivity.KST.SConstruction.coreSMap_zeroVertex
#print axioms SerrePositivity.KST.SConstruction.coreSMap_zeroVertex

#check @SerrePositivity.KST.SConstruction.diagonalCoreSConstruction
#print axioms SerrePositivity.KST.SConstruction.diagonalCoreSConstruction

#check @SerrePositivity.KST.SConstruction.diagonalCoreSConstruction_obj
#print axioms SerrePositivity.KST.SConstruction.diagonalCoreSConstruction_obj

#check @SerrePositivity.KST.SConstruction.diagonalCoreSConstruction_map
#print axioms SerrePositivity.KST.SConstruction.diagonalCoreSConstruction_map

#check @SerrePositivity.KST.SConstruction.kanCoreIso
#print axioms SerrePositivity.KST.SConstruction.kanCoreIso

#check @SerrePositivity.KST.SConstruction.coreSConstructionZero_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.coreSConstructionZero_isContractibleKan

#check @SerrePositivity.KST.SConstruction.pointedCoreSConstruction
#print axioms SerrePositivity.KST.SConstruction.pointedCoreSConstruction

#check @SerrePositivity.KST.SConstruction.pointedCoreSConstruction_kanComplex
#print axioms SerrePositivity.KST.SConstruction.pointedCoreSConstruction_kanComplex

#check @SerrePositivity.KST.SConstruction.pointedCoreSMap
#print axioms SerrePositivity.KST.SConstruction.pointedCoreSMap

#check @SerrePositivity.KST.SConstruction.simplicialPointedCoreSConstruction
#print axioms SerrePositivity.KST.SConstruction.simplicialPointedCoreSConstruction

#check @SerrePositivity.KST.SConstruction.simplicialPointedCoreSConstruction_forget
#print axioms SerrePositivity.KST.SConstruction.simplicialPointedCoreSConstruction_forget

#check @SerrePositivity.KST.SConstruction.pointedSRealization
#print axioms SerrePositivity.KST.SConstruction.pointedSRealization

#check @SerrePositivity.KST.SConstruction.kanSRealization
#print axioms SerrePositivity.KST.SConstruction.kanSRealization

#check @SerrePositivity.KST.SConstruction.kanSRealization_kanComplex
#print axioms SerrePositivity.KST.SConstruction.kanSRealization_kanComplex

#check @SerrePositivity.KST.SConstruction.sRealizationToKan
#print axioms SerrePositivity.KST.SConstruction.sRealizationToKan

#check @SerrePositivity.KST.SConstruction.sRealizationToKan_anodyne
#print axioms SerrePositivity.KST.SConstruction.sRealizationToKan_anodyne

#check @SerrePositivity.KST.SConstruction.kSpace
#print axioms SerrePositivity.KST.SConstruction.kSpace

#check @SerrePositivity.KST.SConstruction.kSpace_kanComplex
#print axioms SerrePositivity.KST.SConstruction.kSpace_kanComplex

#check @SerrePositivity.KST.SConstruction.diagonalZeroColumn
#print axioms SerrePositivity.KST.SConstruction.diagonalZeroColumn

#check @SerrePositivity.KST.SConstruction.diagonalZeroColumn_zero
#print axioms SerrePositivity.KST.SConstruction.diagonalZeroColumn_zero

#check @SerrePositivity.KST.SConstruction.diagonalZeroColumn_piZero_surjective
#print axioms SerrePositivity.KST.SConstruction.diagonalZeroColumn_piZero_surjective

#check @SerrePositivity.KST.SConstruction.diagonal_preconnected_of_zero
#print axioms SerrePositivity.KST.SConstruction.diagonal_preconnected_of_zero

#check @SerrePositivity.KST.SConstruction.diagonal_connected_of_zero
#print axioms SerrePositivity.KST.SConstruction.diagonal_connected_of_zero

#check @SerrePositivity.KST.SConstruction.diagonalCoreSConstruction_isConnected
#print axioms SerrePositivity.KST.SConstruction.diagonalCoreSConstruction_isConnected

#check @SerrePositivity.KST.SConstruction.mapPiZero_bijective_of_anodyne
#print axioms SerrePositivity.KST.SConstruction.mapPiZero_bijective_of_anodyne

#check @SerrePositivity.KST.SConstruction.isConnected_of_anodyne
#print axioms SerrePositivity.KST.SConstruction.isConnected_of_anodyne

#check @SerrePositivity.KST.SConstruction.sRealizationToKan_piZero_bijective
#print axioms SerrePositivity.KST.SConstruction.sRealizationToKan_piZero_bijective

#check @SerrePositivity.KST.SConstruction.kanSRealization_isConnected
#print axioms SerrePositivity.KST.SConstruction.kanSRealization_isConnected

#check @SerrePositivity.KST.SConstruction.pointedOfVertex_kanComplex
#print axioms SerrePositivity.KST.SConstruction.pointedOfVertex_kanComplex

#check @SerrePositivity.KST.SConstruction.pathEvaluation_eq_evaluateFunctorAt
#print axioms SerrePositivity.KST.SConstruction.pathEvaluation_eq_evaluateFunctorAt

#check @SerrePositivity.KST.SConstruction.pointedPathAt
#print axioms SerrePositivity.KST.SConstruction.pointedPathAt

#check @SerrePositivity.KST.SConstruction.pointedPathEndpoint
#print axioms SerrePositivity.KST.SConstruction.pointedPathEndpoint

#check @SerrePositivity.KST.SConstruction.pointedPathAt_kanComplex
#print axioms SerrePositivity.KST.SConstruction.pointedPathAt_kanComplex

#check @SerrePositivity.KST.SConstruction.pointedPathEndpoint_rlp
#print axioms SerrePositivity.KST.SConstruction.pointedPathEndpoint_rlp

#check @SerrePositivity.KST.SConstruction.loopPathEndpoint
#print axioms SerrePositivity.KST.SConstruction.loopPathEndpoint

#check @SerrePositivity.KST.SConstruction.loopPathEndpoint_rlp
#print axioms SerrePositivity.KST.SConstruction.loopPathEndpoint_rlp

#check @SerrePositivity.KST.SConstruction.loopPathEndpoint_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.loopPathEndpoint_piIsomorphism

#check @SerrePositivity.KST.SConstruction.exists_loopBasepointComparison
#print axioms SerrePositivity.KST.SConstruction.exists_loopBasepointComparison

#check @SerrePositivity.KST.SConstruction.kanComparison_congr_left
#print axioms SerrePositivity.KST.SConstruction.kanComparison_congr_left

#check @SerrePositivity.KST.SConstruction.diagonalZeroVertexEdge
#print axioms SerrePositivity.KST.SConstruction.diagonalZeroVertexEdge

#check @SerrePositivity.KST.SConstruction.realizationZeroPoint
#print axioms SerrePositivity.KST.SConstruction.realizationZeroPoint

#check @SerrePositivity.KST.SConstruction.realizationZeroEdge
#print axioms SerrePositivity.KST.SConstruction.realizationZeroEdge

#check @SerrePositivity.KST.SConstruction.kSpaceAtZero
#print axioms SerrePositivity.KST.SConstruction.kSpaceAtZero

#check @SerrePositivity.KST.SConstruction.kSpaceAtZero_kanComplex
#print axioms SerrePositivity.KST.SConstruction.kSpaceAtZero_kanComplex

#check @SerrePositivity.KST.SConstruction.kSpaceAtZero_comparison
#print axioms SerrePositivity.KST.SConstruction.kSpaceAtZero_comparison

#check @SerrePositivity.KST.SConstruction.ofVertex_basepoint_eq
#print axioms SerrePositivity.KST.SConstruction.ofVertex_basepoint_eq

#check @SerrePositivity.KST.SConstruction.realizationZeroPoint_chosen
#print axioms SerrePositivity.KST.SConstruction.realizationZeroPoint_chosen

#check @SerrePositivity.KST.SConstruction.kSpaceAtZero_chosen
#print axioms SerrePositivity.KST.SConstruction.kSpaceAtZero_chosen

#check @SerrePositivity.KST.SConstruction.kSpace_zeroChoice_comparison
#print axioms SerrePositivity.KST.SConstruction.kSpace_zeroChoice_comparison

#check @SerrePositivity.KST.SConstruction.PreservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.PreservesSConstructionData

#check @SerrePositivity.KST.SConstruction.preservesSConstructionData_id
#print axioms SerrePositivity.KST.SConstruction.preservesSConstructionData_id

#check @SerrePositivity.KST.SConstruction.PreservesSConstructionData.comp
#print axioms SerrePositivity.KST.SConstruction.PreservesSConstructionData.comp

#check @SerrePositivity.KST.SConstruction.IsGapped.postcomp
#print axioms SerrePositivity.KST.SConstruction.IsGapped.postcomp

#check @SerrePositivity.KST.SConstruction.sPostcomp
#print axioms SerrePositivity.KST.SConstruction.sPostcomp

#check @SerrePositivity.KST.SConstruction.sPostcomp_ι
#print axioms SerrePositivity.KST.SConstruction.sPostcomp_ι

#check @SerrePositivity.KST.SConstruction.sPostcomp_id
#print axioms SerrePositivity.KST.SConstruction.sPostcomp_id

#check @SerrePositivity.KST.SConstruction.sPostcomp_comp
#print axioms SerrePositivity.KST.SConstruction.sPostcomp_comp

#check @SerrePositivity.KST.SConstruction.sPostcomp_sMap
#print axioms SerrePositivity.KST.SConstruction.sPostcomp_sMap

#check @SerrePositivity.KST.SConstruction.simplicialSPostcomp
#print axioms SerrePositivity.KST.SConstruction.simplicialSPostcomp

#check @SerrePositivity.KST.SConstruction.simplicialCoreSPostcomp
#print axioms SerrePositivity.KST.SConstruction.simplicialCoreSPostcomp

#check @SerrePositivity.KST.SConstruction.diagonalSPostcomp
#print axioms SerrePositivity.KST.SConstruction.diagonalSPostcomp

#check @SerrePositivity.KST.SConstruction.sPostcomp_zeroVertex
#print axioms SerrePositivity.KST.SConstruction.sPostcomp_zeroVertex

#check @SerrePositivity.KST.SConstruction.diagonalSPostcomp_id
#print axioms SerrePositivity.KST.SConstruction.diagonalSPostcomp_id

#check @SerrePositivity.KST.SConstruction.diagonalSPostcomp_comp
#print axioms SerrePositivity.KST.SConstruction.diagonalSPostcomp_comp

#check @SerrePositivity.KST.SConstruction.diagonalSPostcomp_zeroVertex
#print axioms SerrePositivity.KST.SConstruction.diagonalSPostcomp_zeroVertex

#check @SerrePositivity.KST.SConstruction.PreservesChosenZero
#print axioms SerrePositivity.KST.SConstruction.PreservesChosenZero

#check @SerrePositivity.KST.SConstruction.preservesChosenZero_id
#print axioms SerrePositivity.KST.SConstruction.preservesChosenZero_id

#check @SerrePositivity.KST.SConstruction.PreservesChosenZero.comp
#print axioms SerrePositivity.KST.SConstruction.PreservesChosenZero.comp

#check @SerrePositivity.KST.SConstruction.pointedSPostcomp
#print axioms SerrePositivity.KST.SConstruction.pointedSPostcomp

#check @SerrePositivity.KST.SConstruction.pointedSPostcomp_id
#print axioms SerrePositivity.KST.SConstruction.pointedSPostcomp_id

#check @SerrePositivity.KST.SConstruction.pointedSPostcomp_comp
#print axioms SerrePositivity.KST.SConstruction.pointedSPostcomp_comp

#check @SerrePositivity.KST.SConstruction.kanSPostcomp
#print axioms SerrePositivity.KST.SConstruction.kanSPostcomp

#check @SerrePositivity.KST.SConstruction.kSpacePostcomp
#print axioms SerrePositivity.KST.SConstruction.kSpacePostcomp

#check @SerrePositivity.KST.SConstruction.kSpacePostcomp_id
#print axioms SerrePositivity.KST.SConstruction.kSpacePostcomp_id

#check @SerrePositivity.KST.SConstruction.kSpacePostcomp_comp
#print axioms SerrePositivity.KST.SConstruction.kSpacePostcomp_comp

#check @SerrePositivity.KST.SConstruction.iteratedSConstruction
#print axioms SerrePositivity.KST.SConstruction.iteratedSConstruction

#check @SerrePositivity.KST.SConstruction.iteratedSConstruction_quasicategory
#print axioms SerrePositivity.KST.SConstruction.iteratedSConstruction_quasicategory

#check @SerrePositivity.KST.SConstruction.iteratedSConstruction_hasZeroVertex
#print axioms SerrePositivity.KST.SConstruction.iteratedSConstruction_hasZeroVertex

#check @SerrePositivity.KST.SConstruction.iteratedZeroVertex
#print axioms SerrePositivity.KST.SConstruction.iteratedZeroVertex

#check @SerrePositivity.KST.SConstruction.iteratedCoreSConstruction
#print axioms SerrePositivity.KST.SConstruction.iteratedCoreSConstruction

#check @SerrePositivity.KST.SConstruction.iteratedCoreSConstruction_kanComplex
#print axioms SerrePositivity.KST.SConstruction.iteratedCoreSConstruction_kanComplex

#check @SerrePositivity.KST.SConstruction.sConstruction_isZeroVertex_of_contractible
#print axioms SerrePositivity.KST.SConstruction.sConstruction_isZeroVertex_of_contractible

#check @SerrePositivity.KST.SConstruction.sConstruction_isContractibleKan_of_contractible
#print axioms SerrePositivity.KST.SConstruction.sConstruction_isContractibleKan_of_contractible

#check @SerrePositivity.KST.SConstruction.iteratedSConstruction_isContractibleKan_of_zero_mem
#print axioms SerrePositivity.KST.SConstruction.iteratedSConstruction_isContractibleKan_of_zero_mem

#check @SerrePositivity.KST.SConstruction.iteratedCoreSConstruction_isContractibleKan_of_zero_mem
#print axioms SerrePositivity.KST.SConstruction.iteratedCoreSConstruction_isContractibleKan_of_zero_mem

#check @SerrePositivity.KST.SConstruction.mapJoinCocone
#print axioms SerrePositivity.KST.SConstruction.mapJoinCocone

#check @SerrePositivity.KST.SConstruction.sliceUnderPostcomp_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.sliceUnderPostcomp_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.isColimitCone_iff_mapJoinCocone_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_iff_mapJoinCocone_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.isZeroVertex_iff_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.isZeroVertex_iff_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.isPushoutSquare_iff_postcomp_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.isPushoutSquare_iff_postcomp_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.isPullbackSquare_iff_postcomp_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.isPullbackSquare_iff_postcomp_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.preservesSConstructionData_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.preservesSConstructionData_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_preservesSConstructionData

#check @SerrePositivity.KST.SConstruction.squareRightEdge_mono
#print axioms SerrePositivity.KST.SConstruction.squareRightEdge_mono

#check @SerrePositivity.KST.SConstruction.squareBottomEdge_mono
#print axioms SerrePositivity.KST.SConstruction.squareBottomEdge_mono

#check @SerrePositivity.KST.SConstruction.hasZeroVertex_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.hasZeroVertex_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.fiberSquare_nonempty_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.fiberSquare_nonempty_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.cofiberSquare_nonempty_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.cofiberSquare_nonempty_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.isStable_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.isStable_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.terminalBoundaryLifting_of_initialBoundaryLifting_op
#print axioms SerrePositivity.KST.SConstruction.terminalBoundaryLifting_of_initialBoundaryLifting_op

#check @SerrePositivity.KST.SConstruction.TerminalBoundaryLifting.op_initial
#print axioms SerrePositivity.KST.SConstruction.TerminalBoundaryLifting.op_initial

#check @SerrePositivity.KST.SConstruction.TerminalBoundaryLifting.of_vertexIso
#print axioms SerrePositivity.KST.SConstruction.TerminalBoundaryLifting.of_vertexIso

#check @SerrePositivity.KST.SConstruction.exists_terminalConeVertex_over_invertible_edge
#print axioms SerrePositivity.KST.SConstruction.exists_terminalConeVertex_over_invertible_edge

#check @SerrePositivity.KST.SConstruction.HasLimit.of_functorIso
#print axioms SerrePositivity.KST.SConstruction.HasLimit.of_functorIso

#check @SerrePositivity.KST.SConstruction.hasLimit_iff_of_functorIso
#print axioms SerrePositivity.KST.SConstruction.hasLimit_iff_of_functorIso

#check @SerrePositivity.KST.SConstruction.zeroCospanData
#print axioms SerrePositivity.KST.SConstruction.zeroCospanData

#check @SerrePositivity.KST.SConstruction.zeroCospanDataProjection
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDataProjection

#check @SerrePositivity.KST.SConstruction.zeroCospanDataProjection_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDataProjection_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.zeroCospanDataDiagram
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDataDiagram

#check @SerrePositivity.KST.SConstruction.zeroCospanDataDiagram_left
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDataDiagram_left

#check @SerrePositivity.KST.SConstruction.zeroCospanDataDiagram_right
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDataDiagram_right

#check @SerrePositivity.KST.SConstruction.zeroCospan_targets
#print axioms SerrePositivity.KST.SConstruction.zeroCospan_targets

#check @SerrePositivity.KST.SConstruction.zeroCospanDataLift
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDataLift

#check @SerrePositivity.KST.SConstruction.zeroCospanDataLift_projection
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDataLift_projection

#check @SerrePositivity.KST.SConstruction.zeroCospanDataLift_diagram
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDataLift_diagram

#check @SerrePositivity.KST.SConstruction.zeroCospanFamiliesIso
#print axioms SerrePositivity.KST.SConstruction.zeroCospanFamiliesIso

#check @SerrePositivity.KST.SConstruction.zeroCospanDiagramsIso
#print axioms SerrePositivity.KST.SConstruction.zeroCospanDiagramsIso

#check @SerrePositivity.KST.SConstruction.hasLimit_zeroCospan
#print axioms SerrePositivity.KST.SConstruction.hasLimit_zeroCospan

#check @SerrePositivity.KST.SConstruction.fiberSquare_nonempty_of_zeroCospan_limits
#print axioms SerrePositivity.KST.SConstruction.fiberSquare_nonempty_of_zeroCospan_limits

#check @SerrePositivity.KST.SConstruction.functor_const_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.functor_const_isZeroVertex

#check @SerrePositivity.KST.SConstruction.functor_hasZeroVertex
#print axioms SerrePositivity.KST.SConstruction.functor_hasZeroVertex

#check @SerrePositivity.KST.SConstruction.isZeroVertex_evaluateFunctorAt
#print axioms SerrePositivity.KST.SConstruction.isZeroVertex_evaluateFunctorAt

#check @SerrePositivity.KST.SConstruction.cofiberFamilySquare_bottomEdge
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilySquare_bottomEdge

#check @SerrePositivity.KST.SConstruction.functor_cofiberSquare_nonempty
#print axioms SerrePositivity.KST.SConstruction.functor_cofiberSquare_nonempty

#check @SerrePositivity.KST.SConstruction.zeroSourceArrow_evaluate
#print axioms SerrePositivity.KST.SConstruction.zeroSourceArrow_evaluate

#check @SerrePositivity.KST.SConstruction.zeroTargetArrow_evaluate
#print axioms SerrePositivity.KST.SConstruction.zeroTargetArrow_evaluate

#check @SerrePositivity.KST.SConstruction.functor_zeroCospan_hasPointwiseLimits
#print axioms SerrePositivity.KST.SConstruction.functor_zeroCospan_hasPointwiseLimits

#check @SerrePositivity.KST.SConstruction.functor_zeroSpan_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.functor_zeroSpan_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.functor_fiberSquare_nonempty
#print axioms SerrePositivity.KST.SConstruction.functor_fiberSquare_nonempty

#check @SerrePositivity.KST.SConstruction.functor_zeroTriangle_pullback_iff
#print axioms SerrePositivity.KST.SConstruction.functor_zeroTriangle_pullback_iff

#check @SerrePositivity.KST.SConstruction.functor_zeroTriangle_pushout_iff
#print axioms SerrePositivity.KST.SConstruction.functor_zeroTriangle_pushout_iff

#check @SerrePositivity.KST.SConstruction.functor_isStable
#print axioms SerrePositivity.KST.SConstruction.functor_isStable

#check @SerrePositivity.KST.SConstruction.sConstruction_isStable
#print axioms SerrePositivity.KST.SConstruction.sConstruction_isStable

#check @SerrePositivity.KST.SConstruction.iteratedSConstruction_isStable
#print axioms SerrePositivity.KST.SConstruction.iteratedSConstruction_isStable

#check @SerrePositivity.KST.SConstruction.map_isZeroVertex_of_zero_image
#print axioms SerrePositivity.KST.SConstruction.map_isZeroVertex_of_zero_image

#check @SerrePositivity.KST.SConstruction.gappedInclusion_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.gappedInclusion_isZeroVertex

#check @SerrePositivity.KST.SConstruction.sMap_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.sMap_isZeroVertex

#check @SerrePositivity.KST.SConstruction.sPostcomp_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.sPostcomp_isZeroVertex

#check @SerrePositivity.KST.SConstruction.ihom_postcomp_evaluate
#print axioms SerrePositivity.KST.SConstruction.ihom_postcomp_evaluate

#check @SerrePositivity.KST.SConstruction.functor_reindex_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.functor_reindex_isZeroVertex

#check @SerrePositivity.KST.SConstruction.functor_postcomp_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.functor_postcomp_isZeroVertex

#check @SerrePositivity.KST.SConstruction.functor_reindex_preserves_cofiber
#print axioms SerrePositivity.KST.SConstruction.functor_reindex_preserves_cofiber

#check @SerrePositivity.KST.SConstruction.functor_postcomp_preserves_cofiber
#print axioms SerrePositivity.KST.SConstruction.functor_postcomp_preserves_cofiber

#check @SerrePositivity.KST.SConstruction.InitialBoundaryLifting.comp
#print axioms SerrePositivity.KST.SConstruction.InitialBoundaryLifting.comp

#check @SerrePositivity.KST.SConstruction.TerminalBoundaryLifting.comp
#print axioms SerrePositivity.KST.SConstruction.TerminalBoundaryLifting.comp

#check @SerrePositivity.KST.SConstruction.relativeInitialVertexIso
#print axioms SerrePositivity.KST.SConstruction.relativeInitialVertexIso

#check @SerrePositivity.KST.SConstruction.ihom_pre_innerFibration
#print axioms SerrePositivity.KST.SConstruction.ihom_pre_innerFibration

#check @SerrePositivity.KST.SConstruction.doubleCoconeRestriction
#print axioms SerrePositivity.KST.SConstruction.doubleCoconeRestriction

#check @SerrePositivity.KST.SConstruction.doubleCoconeRestriction_innerFibration
#print axioms SerrePositivity.KST.SConstruction.doubleCoconeRestriction_innerFibration

#check @SerrePositivity.KST.SConstruction.doubleCoconeRestriction_otherOrder
#print axioms SerrePositivity.KST.SConstruction.doubleCoconeRestriction_otherOrder

#check @SerrePositivity.KST.SConstruction.doubleCocone_initial_outer_inner
#print axioms SerrePositivity.KST.SConstruction.doubleCocone_initial_outer_inner

#check @SerrePositivity.KST.SConstruction.doubleCocone_initial_inner_outer
#print axioms SerrePositivity.KST.SConstruction.doubleCocone_initial_inner_outer

#check @SerrePositivity.KST.SConstruction.doubleCoconeUniversalIso
#print axioms SerrePositivity.KST.SConstruction.doubleCoconeUniversalIso

#check @SerrePositivity.KST.SConstruction.colimitInterchange_initialBoundary
#print axioms SerrePositivity.KST.SConstruction.colimitInterchange_initialBoundary

#check @SerrePositivity.KST.SConstruction.colimitCoconeIsoOfDiagramIso
#print axioms SerrePositivity.KST.SConstruction.colimitCoconeIsoOfDiagramIso

#check @SerrePositivity.KST.SConstruction.pushoutSquareIsoOfSpanIso
#print axioms SerrePositivity.KST.SConstruction.pushoutSquareIsoOfSpanIso

#check @SerrePositivity.KST.SConstruction.isZeroVertex_pushout_apex_of_zeroSpan
#print axioms SerrePositivity.KST.SConstruction.isZeroVertex_pushout_apex_of_zeroSpan

#check @SerrePositivity.KST.SConstruction.IsGapped.of_functorIso
#print axioms SerrePositivity.KST.SConstruction.IsGapped.of_functorIso

#check @SerrePositivity.KST.SConstruction.isGapped_iff_of_functorIso
#print axioms SerrePositivity.KST.SConstruction.isGapped_iff_of_functorIso

#check @SerrePositivity.KST.SConstruction.isGapped_of_functorVertex_isZero
#print axioms SerrePositivity.KST.SConstruction.isGapped_of_functorVertex_isZero

#check @SerrePositivity.KST.SConstruction.squareDiagram_pre
#print axioms SerrePositivity.KST.SConstruction.squareDiagram_pre

#check @SerrePositivity.KST.SConstruction.squareDiagram_pushout_iff_initialBoundary
#print axioms SerrePositivity.KST.SConstruction.squareDiagram_pushout_iff_initialBoundary

#check @SerrePositivity.KST.SConstruction.pushoutInterchange
#print axioms SerrePositivity.KST.SConstruction.pushoutInterchange

#check @SerrePositivity.KST.SConstruction.zeroSpanColimit_functorVertex_isZero
#print axioms SerrePositivity.KST.SConstruction.zeroSpanColimit_functorVertex_isZero

#check @SerrePositivity.KST.SConstruction.zeroSpanColimit_all_vertices_zero
#print axioms SerrePositivity.KST.SConstruction.zeroSpanColimit_all_vertices_zero

#check @SerrePositivity.KST.SConstruction.functorVertexEquiv_symm_evaluate
#print axioms SerrePositivity.KST.SConstruction.functorVertexEquiv_symm_evaluate

#check @SerrePositivity.KST.SConstruction.functorVertexEquiv_symm_pre
#print axioms SerrePositivity.KST.SConstruction.functorVertexEquiv_symm_pre

#check @SerrePositivity.KST.SConstruction.gapped_pointwiseColimit_zero_diagonal
#print axioms SerrePositivity.KST.SConstruction.gapped_pointwiseColimit_zero_diagonal

#check @SerrePositivity.KST.SConstruction.gapped_pointwiseColimit
#print axioms SerrePositivity.KST.SConstruction.gapped_pointwiseColimit

#check @SerrePositivity.KST.SConstruction.ihom_fullSubcomplex_hasLiftingProperty_of_vertexSurjective
#print axioms SerrePositivity.KST.SConstruction.ihom_fullSubcomplex_hasLiftingProperty_of_vertexSurjective

#check @SerrePositivity.KST.SConstruction.initialBoundaryLifting_reflect_of_boundary_lifting
#print axioms SerrePositivity.KST.SConstruction.initialBoundaryLifting_reflect_of_boundary_lifting

#check @SerrePositivity.KST.SConstruction.isColimitCone_fullSubcomplex_of_ambient
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_fullSubcomplex_of_ambient

#check @SerrePositivity.KST.SConstruction.exists_gapped_pointwiseColimitCocone
#print axioms SerrePositivity.KST.SConstruction.exists_gapped_pointwiseColimitCocone

#check @SerrePositivity.KST.SConstruction.isColimitCone_gapped_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_gapped_of_pointwise

#check @SerrePositivity.KST.SConstruction.isPointwiseColimitCone_gappedInclusion_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.isPointwiseColimitCone_gappedInclusion_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.isColimitCone_gappedInclusion_iff_of_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.isColimitCone_gappedInclusion_iff_of_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.gappedInclusionZeroTriangle
#print axioms SerrePositivity.KST.SConstruction.gappedInclusionZeroTriangle

#check @SerrePositivity.KST.SConstruction.gappedInclusion_zeroSpan_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.gappedInclusion_zeroSpan_hasPointwiseColimits

#check @SerrePositivity.KST.SConstruction.gappedInclusion_cofiber_iff
#print axioms SerrePositivity.KST.SConstruction.gappedInclusion_cofiber_iff

#check @SerrePositivity.KST.SConstruction.gappedInclusion_cofiber_iff_pointwise
#print axioms SerrePositivity.KST.SConstruction.gappedInclusion_cofiber_iff_pointwise

#check @SerrePositivity.KST.SConstruction.sMap_gapped_evaluate
#print axioms SerrePositivity.KST.SConstruction.sMap_gapped_evaluate

#check @SerrePositivity.KST.SConstruction.sPostcomp_gapped_evaluate
#print axioms SerrePositivity.KST.SConstruction.sPostcomp_gapped_evaluate

#check @SerrePositivity.KST.SConstruction.sMapZeroTriangle
#print axioms SerrePositivity.KST.SConstruction.sMapZeroTriangle

#check @SerrePositivity.KST.SConstruction.sPostcompZeroTriangle
#print axioms SerrePositivity.KST.SConstruction.sPostcompZeroTriangle

#check @SerrePositivity.KST.SConstruction.sMap_preserves_cofiber
#print axioms SerrePositivity.KST.SConstruction.sMap_preserves_cofiber

#check @SerrePositivity.KST.SConstruction.sPostcomp_preserves_cofiber
#print axioms SerrePositivity.KST.SConstruction.sPostcomp_preserves_cofiber

#check @SerrePositivity.KST.SConstruction.PreservesCofiberData
#print axioms SerrePositivity.KST.SConstruction.PreservesCofiberData

#check @SerrePositivity.KST.SConstruction.PreservesSConstructionData.toCofiberData
#print axioms SerrePositivity.KST.SConstruction.PreservesSConstructionData.toCofiberData

#check @SerrePositivity.KST.SConstruction.preservesCofiberData_id
#print axioms SerrePositivity.KST.SConstruction.preservesCofiberData_id

#check @SerrePositivity.KST.SConstruction.PreservesCofiberData.comp
#print axioms SerrePositivity.KST.SConstruction.PreservesCofiberData.comp

#check @SerrePositivity.KST.SConstruction.IsGapped.postcomp_of_cofiber
#print axioms SerrePositivity.KST.SConstruction.IsGapped.postcomp_of_cofiber

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_ι
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_ι

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_eq_sPostcomp
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_eq_sPostcomp

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_gapped_evaluate
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_gapped_evaluate

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_isZeroVertex
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_isZeroVertex

#check @SerrePositivity.KST.SConstruction.preservesCofiberData_sPostcompCofiber
#print axioms SerrePositivity.KST.SConstruction.preservesCofiberData_sPostcompCofiber

#check @SerrePositivity.KST.SConstruction.preservesCofiberData_sMap
#print axioms SerrePositivity.KST.SConstruction.preservesCofiberData_sMap

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_id
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_id

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_comp
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_comp

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_sMap
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_sMap

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_zeroVertex
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_zeroVertex

#check @SerrePositivity.KST.SConstruction.StableModel
#print axioms SerrePositivity.KST.SConstruction.StableModel

#check @SerrePositivity.KST.SConstruction.stableModelCategory
#print axioms SerrePositivity.KST.SConstruction.stableModelCategory

#check @SerrePositivity.KST.SConstruction.stableModelForget
#print axioms SerrePositivity.KST.SConstruction.stableModelForget

#check @SerrePositivity.KST.SConstruction.sStableModel
#print axioms SerrePositivity.KST.SConstruction.sStableModel

#check @SerrePositivity.KST.SConstruction.sEndofunctor
#print axioms SerrePositivity.KST.SConstruction.sEndofunctor

#check @SerrePositivity.KST.SConstruction.sEndofunctorMap
#print axioms SerrePositivity.KST.SConstruction.sEndofunctorMap

#check @SerrePositivity.KST.SConstruction.simplicialStableEndofunctor
#print axioms SerrePositivity.KST.SConstruction.simplicialStableEndofunctor

#check @SerrePositivity.KST.SConstruction.multiSEndofunctor
#print axioms SerrePositivity.KST.SConstruction.multiSEndofunctor

#check @SerrePositivity.KST.SConstruction.multiSConstruction
#print axioms SerrePositivity.KST.SConstruction.multiSConstruction

#check @SerrePositivity.KST.SConstruction.multiSConstruction_quasicategory
#print axioms SerrePositivity.KST.SConstruction.multiSConstruction_quasicategory

#check @SerrePositivity.KST.SConstruction.multiSConstruction_isStable
#print axioms SerrePositivity.KST.SConstruction.multiSConstruction_isStable

#check @SerrePositivity.KST.SConstruction.multiSConstruction_obj_succ
#print axioms SerrePositivity.KST.SConstruction.multiSConstruction_obj_succ

#check @SerrePositivity.KST.SConstruction.multiSConstruction_obj_eq_iterated
#print axioms SerrePositivity.KST.SConstruction.multiSConstruction_obj_eq_iterated

#check @SerrePositivity.KST.SConstruction.multiCoreSConstruction
#print axioms SerrePositivity.KST.SConstruction.multiCoreSConstruction

#check @SerrePositivity.KST.SConstruction.multiCoreSConstruction_kanComplex
#print axioms SerrePositivity.KST.SConstruction.multiCoreSConstruction_kanComplex

#check @SerrePositivity.KST.SConstruction.multiSConstruction_isContractibleKan_of_zero_coordinate
#print axioms SerrePositivity.KST.SConstruction.multiSConstruction_isContractibleKan_of_zero_coordinate

#check @SerrePositivity.KST.SConstruction.multiCoreSConstruction_isContractibleKan_of_zero_coordinate
#print axioms SerrePositivity.KST.SConstruction.multiCoreSConstruction_isContractibleKan_of_zero_coordinate

#check @SerrePositivity.KST.SConstruction.multiSConstructionFunctor
#print axioms SerrePositivity.KST.SConstruction.multiSConstructionFunctor

#check @SerrePositivity.KST.SConstruction.multiSConstructionFunctor_obj
#print axioms SerrePositivity.KST.SConstruction.multiSConstructionFunctor_obj

#check @SerrePositivity.KST.SConstruction.multiCoreSConstructionFunctor
#print axioms SerrePositivity.KST.SConstruction.multiCoreSConstructionFunctor

#check @SerrePositivity.KST.SConstruction.multiCoreSConstructionFunctor_obj
#print axioms SerrePositivity.KST.SConstruction.multiCoreSConstructionFunctor_obj

#check @SerrePositivity.KST.SConstruction.multiIndexDiagonal
#print axioms SerrePositivity.KST.SConstruction.multiIndexDiagonal

#check @SerrePositivity.KST.SConstruction.multiDiagonalFunctor
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalFunctor

#check @SerrePositivity.KST.SConstruction.multiRealizationFunctor
#print axioms SerrePositivity.KST.SConstruction.multiRealizationFunctor

#check @SerrePositivity.KST.SConstruction.multiDiagonalCoreSConstruction
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalCoreSConstruction

#check @SerrePositivity.KST.SConstruction.multiDiagonalCoreSConstruction_obj
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalCoreSConstruction_obj

#check @SerrePositivity.KST.SConstruction.StableModel.mk
#print axioms SerrePositivity.KST.SConstruction.StableModel.mk

#check @SerrePositivity.KST.SConstruction.StableModel.carrier
#print axioms SerrePositivity.KST.SConstruction.StableModel.carrier

#check @SerrePositivity.KST.SConstruction.StableModel.quasicategory
#print axioms SerrePositivity.KST.SConstruction.StableModel.quasicategory

#check @SerrePositivity.KST.SConstruction.StableModel.stable
#print axioms SerrePositivity.KST.SConstruction.StableModel.stable

#check @SerrePositivity.KST.SConstruction.simplicialDiagonalFunctor
#print axioms SerrePositivity.KST.SConstruction.simplicialDiagonalFunctor

#check @SerrePositivity.KST.SConstruction.diagonalZeroColumn_mono
#print axioms SerrePositivity.KST.SConstruction.diagonalZeroColumn_mono

#check @SerrePositivity.KST.SConstruction.diagonalZeroColumnNat
#print axioms SerrePositivity.KST.SConstruction.diagonalZeroColumnNat

#check @SerrePositivity.KST.SConstruction.reducedDiagonal
#print axioms SerrePositivity.KST.SConstruction.reducedDiagonal

#check @SerrePositivity.KST.SConstruction.diagonalReductionQuotient
#print axioms SerrePositivity.KST.SConstruction.diagonalReductionQuotient

#check @SerrePositivity.KST.SConstruction.reducedDiagonalMap
#print axioms SerrePositivity.KST.SConstruction.reducedDiagonalMap

#check @SerrePositivity.KST.SConstruction.reducedDiagonalMap_quotient
#print axioms SerrePositivity.KST.SConstruction.reducedDiagonalMap_quotient

#check @SerrePositivity.KST.SConstruction.reducedDiagonalFunctor
#print axioms SerrePositivity.KST.SConstruction.reducedDiagonalFunctor

#check @SerrePositivity.KST.SConstruction.diagonalReductionNat
#print axioms SerrePositivity.KST.SConstruction.diagonalReductionNat

#check @SerrePositivity.KST.SConstruction.map_isIso_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.map_isIso_of_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.trivialKanFibration_toUnit_of_contractible
#print axioms SerrePositivity.KST.SConstruction.trivialKanFibration_toUnit_of_contractible

#check @SerrePositivity.KST.SConstruction.cofiberQuotient_image_isIso_of_contractible
#print axioms SerrePositivity.KST.SConstruction.cofiberQuotient_image_isIso_of_contractible

#check @SerrePositivity.KST.SConstruction.diagonalReductionQuotient_image_isIso
#print axioms SerrePositivity.KST.SConstruction.diagonalReductionQuotient_image_isIso

#check @SerrePositivity.KST.SConstruction.kanPiIsomorphism_of_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.kanPiIsomorphism_of_localized_isIso

#check @SerrePositivity.KST.SConstruction.pointedKanReplacement_map_piIsomorphism_of_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.pointedKanReplacement_map_piIsomorphism_of_localized_isIso

#check @SerrePositivity.KST.SConstruction.multiDiagonalDiagramFunctor
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalDiagramFunctor

#check @SerrePositivity.KST.SConstruction.multiDiagonalDiagram_zero_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalDiagram_zero_isContractibleKan

#check @SerrePositivity.KST.SConstruction.reducedMultiRealizationFunctor
#print axioms SerrePositivity.KST.SConstruction.reducedMultiRealizationFunctor

#check @SerrePositivity.KST.SConstruction.multiRealizationReductionNat
#print axioms SerrePositivity.KST.SConstruction.multiRealizationReductionNat

#check @SerrePositivity.KST.SConstruction.multiRealizationReduction_image_isIso
#print axioms SerrePositivity.KST.SConstruction.multiRealizationReduction_image_isIso

#check @SerrePositivity.KST.SConstruction.reducedMultiKanRealizationFunctor
#print axioms SerrePositivity.KST.SConstruction.reducedMultiKanRealizationFunctor

#check @SerrePositivity.KST.SConstruction.reducedMultiKanRealization_kanComplex
#print axioms SerrePositivity.KST.SConstruction.reducedMultiKanRealization_kanComplex

#check @SerrePositivity.KST.SConstruction.reducedKSpaceFunctor
#print axioms SerrePositivity.KST.SConstruction.reducedKSpaceFunctor

#check @SerrePositivity.KST.SConstruction.reducedKSpaceFunctor_kanComplex
#print axioms SerrePositivity.KST.SConstruction.reducedKSpaceFunctor_kanComplex

#check @SerrePositivity.KST.SConstruction.diagonalReductionPointedMap
#print axioms SerrePositivity.KST.SConstruction.diagonalReductionPointedMap

#check @SerrePositivity.KST.SConstruction.diagonalReductionPointedMap_kan_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.diagonalReductionPointedMap_kan_piIsomorphism

#check @SerrePositivity.KST.SConstruction.diagonalReductionLoopMap
#print axioms SerrePositivity.KST.SConstruction.diagonalReductionLoopMap

#check @SerrePositivity.KST.SConstruction.diagonalReductionLoopMap_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.diagonalReductionLoopMap_piIsomorphism

#check @SerrePositivity.KST.SConstruction.multiDiagonalDiagramFunctor_one_obj
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalDiagramFunctor_one_obj

#check @SerrePositivity.KST.SConstruction.reducedSRealizationComparison
#print axioms SerrePositivity.KST.SConstruction.reducedSRealizationComparison

#check @SerrePositivity.KST.SConstruction.reducedSRealizationComparison_kan_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.reducedSRealizationComparison_kan_piIsomorphism

#check @SerrePositivity.KST.SConstruction.kSpaceReductionComparison
#print axioms SerrePositivity.KST.SConstruction.kSpaceReductionComparison

#check @SerrePositivity.KST.SConstruction.kSpaceReductionComparison_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.kSpaceReductionComparison_piIsomorphism

#check @SerrePositivity.KST.SConstruction.reducedSRealizationComparison_naturality
#print axioms SerrePositivity.KST.SConstruction.reducedSRealizationComparison_naturality

#check @SerrePositivity.KST.SConstruction.kSpaceReductionComparison_naturality
#print axioms SerrePositivity.KST.SConstruction.kSpaceReductionComparison_naturality

#check @SerrePositivity.KST.SConstruction.zeroCoordinateFunctor
#print axioms SerrePositivity.KST.SConstruction.zeroCoordinateFunctor

#check @SerrePositivity.KST.SConstruction.zeroCoordinateNat
#print axioms SerrePositivity.KST.SConstruction.zeroCoordinateNat

#check @SerrePositivity.KST.SConstruction.zeroCoordinateRetraction
#print axioms SerrePositivity.KST.SConstruction.zeroCoordinateRetraction

#check @SerrePositivity.KST.SConstruction.zeroCoordinateNat_retraction
#print axioms SerrePositivity.KST.SConstruction.zeroCoordinateNat_retraction

#check @SerrePositivity.KST.SConstruction.zeroDirectionsIndex
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsIndex

#check @SerrePositivity.KST.SConstruction.zeroDirectionsIndexNat
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsIndexNat

#check @SerrePositivity.KST.SConstruction.zeroDirectionsIndexRetraction
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsIndexRetraction

#check @SerrePositivity.KST.SConstruction.zeroDirectionsIndexNat_retraction
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsIndexNat_retraction

#check @SerrePositivity.KST.SConstruction.zeroDirectionsDiagram
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsDiagram

#check @SerrePositivity.KST.SConstruction.zeroDirectionsDiagramMap
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsDiagramMap

#check @SerrePositivity.KST.SConstruction.zeroDirectionsInclusion
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsInclusion

#check @SerrePositivity.KST.SConstruction.zeroDirectionsInclusion_mono
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsInclusion_mono

#check @SerrePositivity.KST.SConstruction.zeroDirectionsDiagram_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsDiagram_isContractibleKan

#check @SerrePositivity.KST.SConstruction.zeroCoordinateEndomorphism
#print axioms SerrePositivity.KST.SConstruction.zeroCoordinateEndomorphism

#check @SerrePositivity.KST.SConstruction.zeroCoordinateEndomorphism_or
#print axioms SerrePositivity.KST.SConstruction.zeroCoordinateEndomorphism_or

#check @SerrePositivity.KST.SConstruction.zeroDirectionsIndexEndomorphism
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsIndexEndomorphism

#check @SerrePositivity.KST.SConstruction.zeroDirectionsIndexEndomorphism_union
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsIndexEndomorphism_union

#check @SerrePositivity.KST.SConstruction.zeroDirectionsRetractionAt
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsRetractionAt

#check @SerrePositivity.KST.SConstruction.zeroDirectionsRetractionAt_leftInverse
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsRetractionAt_leftInverse

#check @SerrePositivity.KST.SConstruction.zeroDirectionsOperator
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsOperator

#check @SerrePositivity.KST.SConstruction.zeroDirectionsOperator_eq_map
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsOperator_eq_map

#check @SerrePositivity.KST.SConstruction.zeroDirectionsOperator_union
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsOperator_union

#check @SerrePositivity.KST.SConstruction.zeroDirectionsRange
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsRange

#check @SerrePositivity.KST.SConstruction.mem_zeroDirectionsRange_iff
#print axioms SerrePositivity.KST.SConstruction.mem_zeroDirectionsRange_iff

#check @SerrePositivity.KST.SConstruction.zeroDirectionsRange_antitone
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsRange_antitone

#check @SerrePositivity.KST.SConstruction.zeroDirectionsRange_union
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsRange_union

#check @SerrePositivity.KST.SConstruction.zeroDirectionsDiagramToPoint
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsDiagramToPoint

#check @SerrePositivity.KST.SConstruction.zeroDirectionsRealization_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsRealization_toPoint_localized_isIso

#check @SerrePositivity.KST.SConstruction.zeroDirectionsRealization_toPoint_image_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsRealization_toPoint_image_isIso

#check @SerrePositivity.KST.SConstruction.zeroDirectionsRange_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsRange_toPoint_localized_isIso

#check @SerrePositivity.KST.SConstruction.subcomplex_inf_sup
#print axioms SerrePositivity.KST.SConstruction.subcomplex_inf_sup

#check @SerrePositivity.KST.SConstruction.subcomplex_sup_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.subcomplex_sup_toPoint_localized_isIso

#check @SerrePositivity.KST.SConstruction.zeroDirectionsBoundary
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsBoundary

#check @SerrePositivity.KST.SConstruction.zeroDirectionsBoundary_insert
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsBoundary_insert

#check @SerrePositivity.KST.SConstruction.zeroDirectionsBoundary_inf
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsBoundary_inf

#check @SerrePositivity.KST.SConstruction.zeroDirectionsBoundary_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsBoundary_toPoint_localized_isIso

#check @SerrePositivity.KST.SConstruction.zeroDirectionsFatBoundary
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsFatBoundary

#check @SerrePositivity.KST.SConstruction.zeroDirectionsFatBoundary_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsFatBoundary_toPoint_localized_isIso

#check @SerrePositivity.KST.SConstruction.zeroDirectionsRealizationFunctor
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsRealizationFunctor

#check @SerrePositivity.KST.SConstruction.zeroDirectionsInclusionNat
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsInclusionNat

#check @SerrePositivity.KST.SConstruction.zeroDirectionsInclusionNat_app
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsInclusionNat_app

#check @SerrePositivity.KST.SConstruction.zeroDirectionsRange_image_le
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsRange_image_le

#check @SerrePositivity.KST.SConstruction.zeroDirectionsBoundary_image_le
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsBoundary_image_le

#check @SerrePositivity.KST.SConstruction.zeroDirectionsFatBoundaryMap
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsFatBoundaryMap

#check @SerrePositivity.KST.SConstruction.zeroDirectionsFatBoundaryMap_ι
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsFatBoundaryMap_ι

#check @SerrePositivity.KST.SConstruction.boundaryReducedRealization
#print axioms SerrePositivity.KST.SConstruction.boundaryReducedRealization

#check @SerrePositivity.KST.SConstruction.boundaryReductionQuotient
#print axioms SerrePositivity.KST.SConstruction.boundaryReductionQuotient

#check @SerrePositivity.KST.SConstruction.boundaryReducedRealizationMap
#print axioms SerrePositivity.KST.SConstruction.boundaryReducedRealizationMap

#check @SerrePositivity.KST.SConstruction.boundaryReducedRealizationMap_quotient
#print axioms SerrePositivity.KST.SConstruction.boundaryReducedRealizationMap_quotient

#check @SerrePositivity.KST.SConstruction.boundaryReducedRealizationFunctor
#print axioms SerrePositivity.KST.SConstruction.boundaryReducedRealizationFunctor

#check @SerrePositivity.KST.SConstruction.boundaryReductionNat
#print axioms SerrePositivity.KST.SConstruction.boundaryReductionNat

#check @SerrePositivity.KST.SConstruction.boundaryReductionQuotient_image_isIso
#print axioms SerrePositivity.KST.SConstruction.boundaryReductionQuotient_image_isIso

#check @SerrePositivity.KST.SConstruction.boundaryKanRealizationFunctor
#print axioms SerrePositivity.KST.SConstruction.boundaryKanRealizationFunctor

#check @SerrePositivity.KST.SConstruction.boundaryKanRealization_kanComplex
#print axioms SerrePositivity.KST.SConstruction.boundaryKanRealization_kanComplex

#check @SerrePositivity.KST.SConstruction.cofiberQuotient_image_isIso_of_localized_toPoint
#print axioms SerrePositivity.KST.SConstruction.cofiberQuotient_image_isIso_of_localized_toPoint

#check @SerrePositivity.KST.SConstruction.zeroDirectionsIndexEndomorphism_zero
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsIndexEndomorphism_zero

#check @SerrePositivity.KST.SConstruction.vertex_mem_zeroDirectionsRange
#print axioms SerrePositivity.KST.SConstruction.vertex_mem_zeroDirectionsRange

#check @SerrePositivity.KST.SConstruction.vertex_mem_zeroDirectionsFatBoundary
#print axioms SerrePositivity.KST.SConstruction.vertex_mem_zeroDirectionsFatBoundary

#check @SerrePositivity.KST.SConstruction.cofiberPointedProjection
#print axioms SerrePositivity.KST.SConstruction.cofiberPointedProjection

#check @SerrePositivity.KST.SConstruction.boundaryReductionPointedMap
#print axioms SerrePositivity.KST.SConstruction.boundaryReductionPointedMap

#check @SerrePositivity.KST.SConstruction.boundaryReductionPointedMap_kan_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.boundaryReductionPointedMap_kan_piIsomorphism

#check @SerrePositivity.KST.SConstruction.boundaryReductionLoopMap
#print axioms SerrePositivity.KST.SConstruction.boundaryReductionLoopMap

#check @SerrePositivity.KST.SConstruction.boundaryReductionLoopMap_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.boundaryReductionLoopMap_piIsomorphism

#check @SerrePositivity.KST.SConstruction.boundaryKSpaceFunctor
#print axioms SerrePositivity.KST.SConstruction.boundaryKSpaceFunctor

#check @SerrePositivity.KST.SConstruction.boundaryKSpaceFunctor_kanComplex
#print axioms SerrePositivity.KST.SConstruction.boundaryKSpaceFunctor_kanComplex

#check @SerrePositivity.KST.SConstruction.boundarySRealizationComparison
#print axioms SerrePositivity.KST.SConstruction.boundarySRealizationComparison

#check @SerrePositivity.KST.SConstruction.boundarySRealizationComparison_kan_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.boundarySRealizationComparison_kan_piIsomorphism

#check @SerrePositivity.KST.SConstruction.kSpaceBoundaryComparison
#print axioms SerrePositivity.KST.SConstruction.kSpaceBoundaryComparison

#check @SerrePositivity.KST.SConstruction.kSpaceBoundaryComparison_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.kSpaceBoundaryComparison_piIsomorphism

#check @SerrePositivity.KST.SConstruction.boundarySRealizationComparison_naturality
#print axioms SerrePositivity.KST.SConstruction.boundarySRealizationComparison_naturality

#check @SerrePositivity.KST.SConstruction.kSpaceBoundaryComparison_naturality
#print axioms SerrePositivity.KST.SConstruction.kSpaceBoundaryComparison_naturality

#check @SerrePositivity.KST.SConstruction.diagonalAssembly
#print axioms SerrePositivity.KST.SConstruction.diagonalAssembly

#check @SerrePositivity.KST.SConstruction.diagonalAssembly_naturality
#print axioms SerrePositivity.KST.SConstruction.diagonalAssembly_naturality

#check @SerrePositivity.KST.SConstruction.diagonalAssembly_reindex
#print axioms SerrePositivity.KST.SConstruction.diagonalAssembly_reindex

#check @SerrePositivity.KST.SConstruction.diagonalAssembly_zero
#print axioms SerrePositivity.KST.SConstruction.diagonalAssembly_zero

#check @SerrePositivity.KST.SConstruction.diagonalAssembly_endpoint
#print axioms SerrePositivity.KST.SConstruction.diagonalAssembly_endpoint

#check @SerrePositivity.KST.SConstruction.diagonalAssembly_endpoint_reduced
#print axioms SerrePositivity.KST.SConstruction.diagonalAssembly_endpoint_reduced

#check @SerrePositivity.KST.SConstruction.intervalBoundary_simplex_constant
#print axioms SerrePositivity.KST.SConstruction.intervalBoundary_simplex_constant

#check @SerrePositivity.KST.SConstruction.diagonalAssembly_interval_boundary
#print axioms SerrePositivity.KST.SConstruction.diagonalAssembly_interval_boundary

#check @SerrePositivity.KST.SConstruction.diagonalIntervalComparison
#print axioms SerrePositivity.KST.SConstruction.diagonalIntervalComparison

#check @SerrePositivity.KST.SConstruction.diagonalIntervalComparison_quotient
#print axioms SerrePositivity.KST.SConstruction.diagonalIntervalComparison_quotient

#check @SerrePositivity.KST.SConstruction.diagonalIntervalMap
#print axioms SerrePositivity.KST.SConstruction.diagonalIntervalMap

#check @SerrePositivity.KST.SConstruction.diagonalIntervalMap_quotient
#print axioms SerrePositivity.KST.SConstruction.diagonalIntervalMap_quotient

#check @SerrePositivity.KST.SConstruction.diagonalIntervalFunctor
#print axioms SerrePositivity.KST.SConstruction.diagonalIntervalFunctor

#check @SerrePositivity.KST.SConstruction.diagonalIntervalComparisonNat
#print axioms SerrePositivity.KST.SConstruction.diagonalIntervalComparisonNat

#check @SerrePositivity.KST.SConstruction.coreMap_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.coreMap_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.firstRowOneUnitIso
#print axioms SerrePositivity.KST.SConstruction.firstRowOneUnitIso

#check @SerrePositivity.KST.SConstruction.firstRowOneHomNatIso
#print axioms SerrePositivity.KST.SConstruction.firstRowOneHomNatIso

#check @SerrePositivity.KST.SConstruction.sOneComparison
#print axioms SerrePositivity.KST.SConstruction.sOneComparison

#check @SerrePositivity.KST.SConstruction.sOneComparison_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.sOneComparison_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.firstRowRestriction_sPostcompCofiber
#print axioms SerrePositivity.KST.SConstruction.firstRowRestriction_sPostcompCofiber

#check @SerrePositivity.KST.SConstruction.sOneComparison_naturality
#print axioms SerrePositivity.KST.SConstruction.sOneComparison_naturality

#check @SerrePositivity.KST.SConstruction.coreSOneComparison
#print axioms SerrePositivity.KST.SConstruction.coreSOneComparison

#check @SerrePositivity.KST.SConstruction.coreSOneComparison_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.coreSOneComparison_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.coreSOneComparison_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.coreSOneComparison_piIsomorphism

#check @SerrePositivity.KST.SConstruction.coreSOneComparison_naturality
#print axioms SerrePositivity.KST.SConstruction.coreSOneComparison_naturality

#check @SerrePositivity.KST.SConstruction.coreSOneComparisonNat
#print axioms SerrePositivity.KST.SConstruction.coreSOneComparisonNat

#check @SerrePositivity.KST.SConstruction.sOneComparison_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.sOneComparison_preservesSConstructionData

#check @SerrePositivity.KST.SConstruction.sOneComparison_preservesCofiberData
#print axioms SerrePositivity.KST.SConstruction.sOneComparison_preservesCofiberData

#check @SerrePositivity.KST.SConstruction.stableSOneComparison
#print axioms SerrePositivity.KST.SConstruction.stableSOneComparison

#check @SerrePositivity.KST.SConstruction.stableSOneComparisonNat
#print axioms SerrePositivity.KST.SConstruction.stableSOneComparisonNat

#check @SerrePositivity.KST.SConstruction.oneDirectionIndex
#print axioms SerrePositivity.KST.SConstruction.oneDirectionIndex

#check @SerrePositivity.KST.SConstruction.multiSOneEndofunctorComparison
#print axioms SerrePositivity.KST.SConstruction.multiSOneEndofunctorComparison

#check @SerrePositivity.KST.SConstruction.multiSOneComparison
#print axioms SerrePositivity.KST.SConstruction.multiSOneComparison

#check @SerrePositivity.KST.SConstruction.multiSOneComparison_app
#print axioms SerrePositivity.KST.SConstruction.multiSOneComparison_app

#check @SerrePositivity.KST.SConstruction.multiSOneComparison_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.multiSOneComparison_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.multiCoreSOneComparison
#print axioms SerrePositivity.KST.SConstruction.multiCoreSOneComparison

#check @SerrePositivity.KST.SConstruction.multiCoreSOneComparison_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.multiCoreSOneComparison_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.oneDirectionDiagonalComparison
#print axioms SerrePositivity.KST.SConstruction.oneDirectionDiagonalComparison

#check @SerrePositivity.KST.SConstruction.oneDirectionRealizationComparison
#print axioms SerrePositivity.KST.SConstruction.oneDirectionRealizationComparison

#check @SerrePositivity.KST.SConstruction.oneDirectionRealizationComparison_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.oneDirectionRealizationComparison_localized_isIso

#check @SerrePositivity.KST.SConstruction.multiSOneComparison_naturality
#print axioms SerrePositivity.KST.SConstruction.multiSOneComparison_naturality

#check @SerrePositivity.KST.SConstruction.multiCoreSOneComparison_naturality
#print axioms SerrePositivity.KST.SConstruction.multiCoreSOneComparison_naturality

#check @SerrePositivity.KST.SConstruction.multiCoreSOneComparisonNat
#print axioms SerrePositivity.KST.SConstruction.multiCoreSOneComparisonNat

#check @SerrePositivity.KST.SConstruction.oneDirectionRealizationFunctor
#print axioms SerrePositivity.KST.SConstruction.oneDirectionRealizationFunctor

#check @SerrePositivity.KST.SConstruction.oneDirectionRealizationComparisonNat
#print axioms SerrePositivity.KST.SConstruction.oneDirectionRealizationComparisonNat

#check @SerrePositivity.KST.SConstruction.oneDirectionRealizationComparisonNat_app
#print axioms SerrePositivity.KST.SConstruction.oneDirectionRealizationComparisonNat_app

#check @SerrePositivity.KST.SConstruction.oneDirectionAssemblyIndex
#print axioms SerrePositivity.KST.SConstruction.oneDirectionAssemblyIndex

#check @SerrePositivity.KST.SConstruction.oneDirectionAssemblyIndex_naturality
#print axioms SerrePositivity.KST.SConstruction.oneDirectionAssemblyIndex_naturality

#check @SerrePositivity.KST.SConstruction.coordinateDiagonalAssembly
#print axioms SerrePositivity.KST.SConstruction.coordinateDiagonalAssembly

#check @SerrePositivity.KST.SConstruction.multiDiagonalAssembly
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalAssembly

#check @SerrePositivity.KST.SConstruction.coordinateDiagonalAssembly_naturality
#print axioms SerrePositivity.KST.SConstruction.coordinateDiagonalAssembly_naturality

#check @SerrePositivity.KST.SConstruction.multiDiagonalAssembly_naturality
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalAssembly_naturality

#check @SerrePositivity.KST.SConstruction.oneDirectionAssemblyIndex_constant_fixed
#print axioms SerrePositivity.KST.SConstruction.oneDirectionAssemblyIndex_constant_fixed

#check @SerrePositivity.KST.SConstruction.multiDiagonalAssembly_constant_mem
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalAssembly_constant_mem

#check @SerrePositivity.KST.SConstruction.multiDiagonalAssembly_boundary_mem
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalAssembly_boundary_mem

#check @SerrePositivity.KST.SConstruction.multiAssemblyBoundaryLift
#print axioms SerrePositivity.KST.SConstruction.multiAssemblyBoundaryLift

#check @SerrePositivity.KST.SConstruction.multiAssemblyBoundaryLift_ι
#print axioms SerrePositivity.KST.SConstruction.multiAssemblyBoundaryLift_ι

#check @SerrePositivity.KST.SConstruction.multiDiagonalAssembly_boundary_condition
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalAssembly_boundary_condition

#check @SerrePositivity.KST.SConstruction.multiIntervalBoundaryComparison
#print axioms SerrePositivity.KST.SConstruction.multiIntervalBoundaryComparison

#check @SerrePositivity.KST.SConstruction.multiIntervalBoundaryComparison_quotient
#print axioms SerrePositivity.KST.SConstruction.multiIntervalBoundaryComparison_quotient

#check @SerrePositivity.KST.SConstruction.intervalBoundaryQuotientFunctor
#print axioms SerrePositivity.KST.SConstruction.intervalBoundaryQuotientFunctor

#check @SerrePositivity.KST.SConstruction.multiIntervalBoundaryFunctor
#print axioms SerrePositivity.KST.SConstruction.multiIntervalBoundaryFunctor

#check @SerrePositivity.KST.SConstruction.multiIntervalBoundaryComparison_naturality
#print axioms SerrePositivity.KST.SConstruction.multiIntervalBoundaryComparison_naturality

#check @SerrePositivity.KST.SConstruction.multiIntervalBoundaryComparisonNat
#print axioms SerrePositivity.KST.SConstruction.multiIntervalBoundaryComparisonNat

#check @SerrePositivity.KST.SConstruction.oneDirectionAssemblyIndex_zero_commute
#print axioms SerrePositivity.KST.SConstruction.oneDirectionAssemblyIndex_zero_commute

#check @SerrePositivity.KST.SConstruction.oneDirectionZeroDiagram
#print axioms SerrePositivity.KST.SConstruction.oneDirectionZeroDiagram

#check @SerrePositivity.KST.SConstruction.oneDirectionZeroInclusion
#print axioms SerrePositivity.KST.SConstruction.oneDirectionZeroInclusion

#check @SerrePositivity.KST.SConstruction.oneDirectionZeroRange
#print axioms SerrePositivity.KST.SConstruction.oneDirectionZeroRange

#check @SerrePositivity.KST.SConstruction.oneDirectionZeroRange_fixed
#print axioms SerrePositivity.KST.SConstruction.oneDirectionZeroRange_fixed

#check @SerrePositivity.KST.SConstruction.multiDiagonalAssembly_zeroRange_mem
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalAssembly_zeroRange_mem

#check @SerrePositivity.KST.SConstruction.oneDirectionFatBoundary
#print axioms SerrePositivity.KST.SConstruction.oneDirectionFatBoundary

#check @SerrePositivity.KST.SConstruction.multiDiagonalAssembly_fatBoundary_mem
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalAssembly_fatBoundary_mem

#check @SerrePositivity.KST.SConstruction.combinedIntervalBoundary
#print axioms SerrePositivity.KST.SConstruction.combinedIntervalBoundary

#check @SerrePositivity.KST.SConstruction.combinedIntervalBoundary_image_le
#print axioms SerrePositivity.KST.SConstruction.combinedIntervalBoundary_image_le

#check @SerrePositivity.KST.SConstruction.combinedAssemblyBoundaryLift
#print axioms SerrePositivity.KST.SConstruction.combinedAssemblyBoundaryLift

#check @SerrePositivity.KST.SConstruction.combinedAssemblyBoundaryLift_ι
#print axioms SerrePositivity.KST.SConstruction.combinedAssemblyBoundaryLift_ι

#check @SerrePositivity.KST.SConstruction.combinedIntervalBoundary_condition
#print axioms SerrePositivity.KST.SConstruction.combinedIntervalBoundary_condition

#check @SerrePositivity.KST.SConstruction.combinedIntervalQuotient
#print axioms SerrePositivity.KST.SConstruction.combinedIntervalQuotient

#check @SerrePositivity.KST.SConstruction.combinedIntervalAssembly
#print axioms SerrePositivity.KST.SConstruction.combinedIntervalAssembly

#check @SerrePositivity.KST.SConstruction.combinedIntervalAssembly_quotient
#print axioms SerrePositivity.KST.SConstruction.combinedIntervalAssembly_quotient

#check @SerrePositivity.KST.SConstruction.oneDirectionZeroRealizationFunctor
#print axioms SerrePositivity.KST.SConstruction.oneDirectionZeroRealizationFunctor

#check @SerrePositivity.KST.SConstruction.diagonalZeroInclusion_naturality
#print axioms SerrePositivity.KST.SConstruction.diagonalZeroInclusion_naturality

#check @SerrePositivity.KST.SConstruction.oneDirectionZeroInclusionNat
#print axioms SerrePositivity.KST.SConstruction.oneDirectionZeroInclusionNat

#check @SerrePositivity.KST.SConstruction.oneDirectionZeroInclusionNat_app
#print axioms SerrePositivity.KST.SConstruction.oneDirectionZeroInclusionNat_app

#check @SerrePositivity.KST.SConstruction.oneDirectionZeroRange_image_le
#print axioms SerrePositivity.KST.SConstruction.oneDirectionZeroRange_image_le

#check @SerrePositivity.KST.SConstruction.oneDirectionFatBoundary_image_le
#print axioms SerrePositivity.KST.SConstruction.oneDirectionFatBoundary_image_le

#check @SerrePositivity.KST.SConstruction.oneDirectionComparison_zeroRange_image_le
#print axioms SerrePositivity.KST.SConstruction.oneDirectionComparison_zeroRange_image_le

#check @SerrePositivity.KST.SConstruction.oneDirectionComparison_fatBoundary_image_le
#print axioms SerrePositivity.KST.SConstruction.oneDirectionComparison_fatBoundary_image_le

#check @SerrePositivity.KST.SConstruction.oneDirectionBoundaryMap
#print axioms SerrePositivity.KST.SConstruction.oneDirectionBoundaryMap

#check @SerrePositivity.KST.SConstruction.oneDirectionBoundaryMap_ι
#print axioms SerrePositivity.KST.SConstruction.oneDirectionBoundaryMap_ι

#check @SerrePositivity.KST.SConstruction.oneDirectionReducedRealization
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReducedRealization

#check @SerrePositivity.KST.SConstruction.oneDirectionReductionQuotient
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReductionQuotient

#check @SerrePositivity.KST.SConstruction.oneDirectionReducedRealizationMap
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReducedRealizationMap

#check @SerrePositivity.KST.SConstruction.oneDirectionReducedRealizationMap_quotient
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReducedRealizationMap_quotient

#check @SerrePositivity.KST.SConstruction.oneDirectionReducedRealizationFunctor
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReducedRealizationFunctor

#check @SerrePositivity.KST.SConstruction.oneDirectionReductionNat
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReductionNat

#check @SerrePositivity.KST.SConstruction.oneDirectionComparisonBoundaryMap
#print axioms SerrePositivity.KST.SConstruction.oneDirectionComparisonBoundaryMap

#check @SerrePositivity.KST.SConstruction.oneDirectionComparisonBoundaryMap_ι
#print axioms SerrePositivity.KST.SConstruction.oneDirectionComparisonBoundaryMap_ι

#check @SerrePositivity.KST.SConstruction.oneDirectionReducedComparison
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReducedComparison

#check @SerrePositivity.KST.SConstruction.oneDirectionReducedComparison_quotient
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReducedComparison_quotient

#check @SerrePositivity.KST.SConstruction.oneDirectionReducedComparison_naturality
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReducedComparison_naturality

#check @SerrePositivity.KST.SConstruction.oneDirectionReducedComparisonNat
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReducedComparisonNat

#check @SerrePositivity.KST.SConstruction.coordinateZeroDiagram
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroDiagram

#check @SerrePositivity.KST.SConstruction.coordinateZeroDiagramMap
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroDiagramMap

#check @SerrePositivity.KST.SConstruction.coordinateZeroInclusion
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroInclusion

#check @SerrePositivity.KST.SConstruction.coordinateZeroInclusion_mono
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroInclusion_mono

#check @SerrePositivity.KST.SConstruction.coordinateZeroRetractionAt
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroRetractionAt

#check @SerrePositivity.KST.SConstruction.coordinateZeroRetractionAt_leftInverse
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroRetractionAt_leftInverse

#check @SerrePositivity.KST.SConstruction.coordinateZeroOperator
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroOperator

#check @SerrePositivity.KST.SConstruction.coordinateZeroOperator_eq_map
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroOperator_eq_map

#check @SerrePositivity.KST.SConstruction.coordinateZeroOperator_union
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroOperator_union

#check @SerrePositivity.KST.SConstruction.coordinateZeroRange
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroRange

#check @SerrePositivity.KST.SConstruction.mem_coordinateZeroRange_iff
#print axioms SerrePositivity.KST.SConstruction.mem_coordinateZeroRange_iff

#check @SerrePositivity.KST.SConstruction.coordinateZeroRange_antitone
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroRange_antitone

#check @SerrePositivity.KST.SConstruction.coordinateZeroRange_union
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroRange_union

#check @SerrePositivity.KST.SConstruction.CoordinateZeroContractible
#print axioms SerrePositivity.KST.SConstruction.CoordinateZeroContractible

#check @SerrePositivity.KST.SConstruction.coordinateZeroDiagramToPoint
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroDiagramToPoint

#check @SerrePositivity.KST.SConstruction.coordinateZeroRealization_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroRealization_toPoint_localized_isIso

#check @SerrePositivity.KST.SConstruction.coordinateZeroRange_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroRange_toPoint_localized_isIso

#check @SerrePositivity.KST.SConstruction.coordinateZeroBoundary
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroBoundary

#check @SerrePositivity.KST.SConstruction.coordinateZeroBoundary_insert
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroBoundary_insert

#check @SerrePositivity.KST.SConstruction.coordinateZeroBoundary_inf
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroBoundary_inf

#check @SerrePositivity.KST.SConstruction.coordinateZeroBoundary_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroBoundary_toPoint_localized_isIso

#check @SerrePositivity.KST.SConstruction.oneDirection_coordinateZeroContractible
#print axioms SerrePositivity.KST.SConstruction.oneDirection_coordinateZeroContractible

#check @SerrePositivity.KST.SConstruction.oneDirectionFatBoundary_eq_coordinate
#print axioms SerrePositivity.KST.SConstruction.oneDirectionFatBoundary_eq_coordinate

#check @SerrePositivity.KST.SConstruction.oneDirectionFatBoundary_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.oneDirectionFatBoundary_toPoint_localized_isIso

#check @SerrePositivity.KST.SConstruction.oneDirectionReductionQuotient_image_isIso
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReductionQuotient_image_isIso

#check @SerrePositivity.KST.SConstruction.oneDirectionReducedComparison_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReducedComparison_localized_isIso

#check @SerrePositivity.KST.SConstruction.oneDirectionReducedComparison_kan_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.oneDirectionReducedComparison_kan_piIsomorphism

#check @SerrePositivity.KST.SConstruction.oneDirectionKanRealizationFunctor
#print axioms SerrePositivity.KST.SConstruction.oneDirectionKanRealizationFunctor

#check @SerrePositivity.KST.SConstruction.oneDirectionKanRealization_kanComplex
#print axioms SerrePositivity.KST.SConstruction.oneDirectionKanRealization_kanComplex

#check @SerrePositivity.KST.SConstruction.oneDirectionKanComparisonNat
#print axioms SerrePositivity.KST.SConstruction.oneDirectionKanComparisonNat

#check @SerrePositivity.KST.SConstruction.oneDirectionLoopComparisonNat
#print axioms SerrePositivity.KST.SConstruction.oneDirectionLoopComparisonNat

#check @SerrePositivity.KST.SConstruction.oneDirectionLoopComparison_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.oneDirectionLoopComparison_piIsomorphism

#check @SerrePositivity.KST.SConstruction.tensorCofiberRightSquare
#print axioms SerrePositivity.KST.SConstruction.tensorCofiberRightSquare

#check @SerrePositivity.KST.SConstruction.tensorCofiberLeftSquare
#print axioms SerrePositivity.KST.SConstruction.tensorCofiberLeftSquare

#check @SerrePositivity.KST.SConstruction.tensorCofiberRightDesc
#print axioms SerrePositivity.KST.SConstruction.tensorCofiberRightDesc

#check @SerrePositivity.KST.SConstruction.tensorCofiberRightDesc_quotient
#print axioms SerrePositivity.KST.SConstruction.tensorCofiberRightDesc_quotient

#check @SerrePositivity.KST.SConstruction.tensorCofiberRightDesc_point
#print axioms SerrePositivity.KST.SConstruction.tensorCofiberRightDesc_point

#check @SerrePositivity.KST.SConstruction.tensorCofiberLeftDesc
#print axioms SerrePositivity.KST.SConstruction.tensorCofiberLeftDesc

#check @SerrePositivity.KST.SConstruction.tensorCofiberLeftDesc_quotient
#print axioms SerrePositivity.KST.SConstruction.tensorCofiberLeftDesc_quotient

#check @SerrePositivity.KST.SConstruction.tensorCofiberRightDesc_left_zero
#print axioms SerrePositivity.KST.SConstruction.tensorCofiberRightDesc_left_zero

#check @SerrePositivity.KST.SConstruction.cofiberTensorDesc
#print axioms SerrePositivity.KST.SConstruction.cofiberTensorDesc

#check @SerrePositivity.KST.SConstruction.cofiberTensorDesc_quotient
#print axioms SerrePositivity.KST.SConstruction.cofiberTensorDesc_quotient

#check @SerrePositivity.KST.SConstruction.adjoinTensorMap
#print axioms SerrePositivity.KST.SConstruction.adjoinTensorMap

#check @SerrePositivity.KST.SConstruction.adjoinTensorMap_precomp
#print axioms SerrePositivity.KST.SConstruction.adjoinTensorMap_precomp

#check @SerrePositivity.KST.SConstruction.adjoinTensorMap_zero
#print axioms SerrePositivity.KST.SConstruction.adjoinTensorMap_zero

#check @SerrePositivity.KST.SConstruction.adjoinTensorMap_left_zero
#print axioms SerrePositivity.KST.SConstruction.adjoinTensorMap_left_zero

#check @SerrePositivity.KST.SConstruction.adjoinTensorMap_right_zero
#print axioms SerrePositivity.KST.SConstruction.adjoinTensorMap_right_zero

#check @SerrePositivity.KST.SConstruction.rawCofiberTensorDesc
#print axioms SerrePositivity.KST.SConstruction.rawCofiberTensorDesc

#check @SerrePositivity.KST.SConstruction.rawCofiberTensorDesc_quotient
#print axioms SerrePositivity.KST.SConstruction.rawCofiberTensorDesc_quotient

#check @SerrePositivity.KST.SConstruction.zeroCylinderAssemblyLift
#print axioms SerrePositivity.KST.SConstruction.zeroCylinderAssemblyLift

#check @SerrePositivity.KST.SConstruction.zeroCylinderAssemblyLift_ι
#print axioms SerrePositivity.KST.SConstruction.zeroCylinderAssemblyLift_ι

#check @SerrePositivity.KST.SConstruction.multiDiagonalAssembly_zeroCylinder_condition
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalAssembly_zeroCylinder_condition

#check @SerrePositivity.KST.SConstruction.oneDirectionSuspensionAssembly
#print axioms SerrePositivity.KST.SConstruction.oneDirectionSuspensionAssembly

#check @SerrePositivity.KST.SConstruction.oneDirectionSuspensionProjection
#print axioms SerrePositivity.KST.SConstruction.oneDirectionSuspensionProjection

#check @SerrePositivity.KST.SConstruction.oneDirectionSuspensionAssembly_quotient
#print axioms SerrePositivity.KST.SConstruction.oneDirectionSuspensionAssembly_quotient

#check @SerrePositivity.KST.SConstruction.cofiberProjection_epi
#print axioms SerrePositivity.KST.SConstruction.cofiberProjection_epi

#check @SerrePositivity.KST.SConstruction.cofiberTensorProjection_epi
#print axioms SerrePositivity.KST.SConstruction.cofiberTensorProjection_epi

#check @SerrePositivity.KST.SConstruction.cofiberTensor_hom_ext
#print axioms SerrePositivity.KST.SConstruction.cofiberTensor_hom_ext

#check @SerrePositivity.KST.SConstruction.cofiberProjection_naturality_of_quotient
#print axioms SerrePositivity.KST.SConstruction.cofiberProjection_naturality_of_quotient

#check @SerrePositivity.KST.SConstruction.adjoinTensorMap_postcomp
#print axioms SerrePositivity.KST.SConstruction.adjoinTensorMap_postcomp

#check @SerrePositivity.KST.SConstruction.oneDirectionSuspensionProjection_epi
#print axioms SerrePositivity.KST.SConstruction.oneDirectionSuspensionProjection_epi

#check @SerrePositivity.KST.SConstruction.oneDirectionCofiberProjection_naturality
#print axioms SerrePositivity.KST.SConstruction.oneDirectionCofiberProjection_naturality

#check @SerrePositivity.KST.SConstruction.oneDirectionSuspensionProjection_naturality
#print axioms SerrePositivity.KST.SConstruction.oneDirectionSuspensionProjection_naturality

#check @SerrePositivity.KST.SConstruction.oneDirectionSuspensionAssembly_naturality
#print axioms SerrePositivity.KST.SConstruction.oneDirectionSuspensionAssembly_naturality

#check @SerrePositivity.KST.SConstruction.oneDirectionSuspensionAssemblyNat
#print axioms SerrePositivity.KST.SConstruction.oneDirectionSuspensionAssemblyNat

#check @SerrePositivity.KST.SConstruction.oneDirectionAssemblyAdjoint
#print axioms SerrePositivity.KST.SConstruction.oneDirectionAssemblyAdjoint

#check @SerrePositivity.KST.SConstruction.oneDirectionAssemblyAdjoint_naturality
#print axioms SerrePositivity.KST.SConstruction.oneDirectionAssemblyAdjoint_naturality

#check @SerrePositivity.KST.SConstruction.oneDirectionAssemblyAdjointNat
#print axioms SerrePositivity.KST.SConstruction.oneDirectionAssemblyAdjointNat

#check @SerrePositivity.KST.SConstruction.oneDirectionAssemblyAdjoint_uncurry
#print axioms SerrePositivity.KST.SConstruction.oneDirectionAssemblyAdjoint_uncurry

#check @SerrePositivity.KST.SConstruction.pointedTransformationArrows
#print axioms SerrePositivity.KST.SConstruction.pointedTransformationArrows

#check @SerrePositivity.KST.SConstruction.pointedTransformationMiddle
#print axioms SerrePositivity.KST.SConstruction.pointedTransformationMiddle

#check @SerrePositivity.KST.SConstruction.pointedTransformationLeft
#print axioms SerrePositivity.KST.SConstruction.pointedTransformationLeft

#check @SerrePositivity.KST.SConstruction.pointedTransformationRight
#print axioms SerrePositivity.KST.SConstruction.pointedTransformationRight

#check @SerrePositivity.KST.SConstruction.pointedTransformation_fac
#print axioms SerrePositivity.KST.SConstruction.pointedTransformation_fac

#check @SerrePositivity.KST.SConstruction.pointedTransformationLeft_mono
#print axioms SerrePositivity.KST.SConstruction.pointedTransformationLeft_mono

#check @SerrePositivity.KST.SConstruction.pointedTransformationRight_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.pointedTransformationRight_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.pointedTransformationMiddle_kanComplex
#print axioms SerrePositivity.KST.SConstruction.pointedTransformationMiddle_kanComplex

#check @SerrePositivity.KST.SConstruction.pointedTransformationRight_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.pointedTransformationRight_piIsomorphism

#check @SerrePositivity.KST.SConstruction.pointedTransformationLeft_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.pointedTransformationLeft_piIsomorphism

#check @SerrePositivity.KST.SConstruction.refinedOneDirectionKanFunctor
#print axioms SerrePositivity.KST.SConstruction.refinedOneDirectionKanFunctor

#check @SerrePositivity.KST.SConstruction.refinedOneDirectionLeftNat
#print axioms SerrePositivity.KST.SConstruction.refinedOneDirectionLeftNat

#check @SerrePositivity.KST.SConstruction.refinedOneDirectionRightNat
#print axioms SerrePositivity.KST.SConstruction.refinedOneDirectionRightNat

#check @SerrePositivity.KST.SConstruction.refinedOneDirection_fac
#print axioms SerrePositivity.KST.SConstruction.refinedOneDirection_fac

#check @SerrePositivity.KST.SConstruction.refinedOneDirectionKan_kanComplex
#print axioms SerrePositivity.KST.SConstruction.refinedOneDirectionKan_kanComplex

#check @SerrePositivity.KST.SConstruction.refinedOneDirectionLeft_mono
#print axioms SerrePositivity.KST.SConstruction.refinedOneDirectionLeft_mono

#check @SerrePositivity.KST.SConstruction.refinedOneDirectionRight_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.refinedOneDirectionRight_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.refinedOneDirectionRight_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.refinedOneDirectionRight_piIsomorphism

#check @SerrePositivity.KST.SConstruction.refinedOneDirectionLeft_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.refinedOneDirectionLeft_piIsomorphism

#check @SerrePositivity.KST.SConstruction.kanTargetSuspensionAssemblyNat
#print axioms SerrePositivity.KST.SConstruction.kanTargetSuspensionAssemblyNat

#check @SerrePositivity.KST.SConstruction.monicSuspensionKanFunctor
#print axioms SerrePositivity.KST.SConstruction.monicSuspensionKanFunctor

#check @SerrePositivity.KST.SConstruction.monicSuspensionAssemblyNat
#print axioms SerrePositivity.KST.SConstruction.monicSuspensionAssemblyNat

#check @SerrePositivity.KST.SConstruction.monicSuspensionComparisonNat
#print axioms SerrePositivity.KST.SConstruction.monicSuspensionComparisonNat

#check @SerrePositivity.KST.SConstruction.monicSuspensionAssembly_fac
#print axioms SerrePositivity.KST.SConstruction.monicSuspensionAssembly_fac

#check @SerrePositivity.KST.SConstruction.monicSuspensionKan_kanComplex
#print axioms SerrePositivity.KST.SConstruction.monicSuspensionKan_kanComplex

#check @SerrePositivity.KST.SConstruction.monicSuspensionAssembly_mono
#print axioms SerrePositivity.KST.SConstruction.monicSuspensionAssembly_mono

#check @SerrePositivity.KST.SConstruction.monicSuspensionComparison_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.monicSuspensionComparison_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.monicSuspensionComparison_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.monicSuspensionComparison_piIsomorphism

#check @SerrePositivity.KST.SConstruction.pointedExtensionSpace
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionSpace

#check @SerrePositivity.KST.SConstruction.pointedExtensionSpace_projection_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionSpace_projection_trivialKanFibration

#check @SerrePositivity.KST.SConstruction.pointedExtensionSpace_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionSpace_isContractibleKan

#check @SerrePositivity.KST.SConstruction.pointedExtensionMap
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionMap

#check @SerrePositivity.KST.SConstruction.pointedExtensionMap_fac
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionMap_fac

#check @SerrePositivity.KST.SConstruction.exists_pointedExtension
#print axioms SerrePositivity.KST.SConstruction.exists_pointedExtension

#check @SerrePositivity.KST.SConstruction.pointedExtensionSpace_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionSpace_relative_lifting

#check @SerrePositivity.KST.SConstruction.loopBoundaryKanFunctor
#print axioms SerrePositivity.KST.SConstruction.loopBoundaryKanFunctor

#check @SerrePositivity.KST.SConstruction.loopBoundaryKan_kanComplex
#print axioms SerrePositivity.KST.SConstruction.loopBoundaryKan_kanComplex

#check @SerrePositivity.KST.SConstruction.kanTargetAssemblyAdjointNat
#print axioms SerrePositivity.KST.SConstruction.kanTargetAssemblyAdjointNat

#check @SerrePositivity.KST.SConstruction.kanAssemblyAdjointChoices
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyAdjointChoices

#check @SerrePositivity.KST.SConstruction.kanAssemblyAdjointChoices_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyAdjointChoices_isContractibleKan

#check @SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt

#check @SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt_fac
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt_fac

#check @SerrePositivity.KST.SConstruction.exists_kanAssemblyAdjoint
#print axioms SerrePositivity.KST.SConstruction.exists_kanAssemblyAdjoint

#check @SerrePositivity.KST.SConstruction.kanAssemblyAdjointChoices_kanComplex
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyAdjointChoices_kanComplex

#check @SerrePositivity.KST.SConstruction.kanAssemblyAdjointChoices_relative_lifting
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyAdjointChoices_relative_lifting

-- Kan 延長のホモトピー比較と全自然数次数の自然性
#check @SerrePositivity.KST.SConstruction.pointedExtensionVertex
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionVertex
#check @SerrePositivity.KST.SConstruction.pointedExtensionVertex_projection
#print axioms SerrePositivity.KST.SConstruction.pointedExtensionVertex_projection
#check @SerrePositivity.KST.SConstruction.pointedExtensions_nonempty_mappingEdge
#print axioms SerrePositivity.KST.SConstruction.pointedExtensions_nonempty_mappingEdge
#check @SerrePositivity.KST.SConstruction.pointedExtensions_homotopy
#print axioms SerrePositivity.KST.SConstruction.pointedExtensions_homotopy
#check @SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt_homotopy
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt_homotopy
#check @SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt_naturality_homotopy
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt_naturality_homotopy
#check @SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt_piMap_eq
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt_piMap_eq
#check @SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt_piMap_naturality
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyAdjointAt_piMap_naturality
#check @SerrePositivity.KST.SConstruction.oneDirectionHomotopyFunctor
#print axioms SerrePositivity.KST.SConstruction.oneDirectionHomotopyFunctor
#check @SerrePositivity.KST.SConstruction.loopBoundaryHomotopyFunctor
#print axioms SerrePositivity.KST.SConstruction.loopBoundaryHomotopyFunctor
#check @SerrePositivity.KST.SConstruction.kanAssemblyHomotopyNat
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyHomotopyNat
#check @SerrePositivity.KST.SConstruction.kanAssemblyHomotopyNat_app
#print axioms SerrePositivity.KST.SConstruction.kanAssemblyHomotopyNat_app

-- 同一の反復 S の Kan 列と K 空間を零段とする列
#check @SerrePositivity.KST.SConstruction.oneDirectionKanComparisonInverse
#print axioms SerrePositivity.KST.SConstruction.oneDirectionKanComparisonInverse
#check @SerrePositivity.KST.SConstruction.oneDirectionKanComparison_inverse_homotopy
#print axioms SerrePositivity.KST.SConstruction.oneDirectionKanComparison_inverse_homotopy
#check @SerrePositivity.KST.SConstruction.oneDirectionKanComparisonInverse_homotopy
#print axioms SerrePositivity.KST.SConstruction.oneDirectionKanComparisonInverse_homotopy
#check @SerrePositivity.KST.SConstruction.oneDirectionKanComparisonInverse_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.oneDirectionKanComparisonInverse_piIsomorphism
#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblyAdjoint
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblyAdjoint
#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblySigma
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblySigma
#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblySigma_adjoint
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblySigma_adjoint
#check @SerrePositivity.KST.SConstruction.boundaryKanSequence
#print axioms SerrePositivity.KST.SConstruction.boundaryKanSequence
#check @SerrePositivity.KST.SConstruction.monicBoundaryKanSequence
#print axioms SerrePositivity.KST.SConstruction.monicBoundaryKanSequence
#check @SerrePositivity.KST.SConstruction.monicBoundaryKanSequence_sigma_mono
#print axioms SerrePositivity.KST.SConstruction.monicBoundaryKanSequence_sigma_mono
#check @SerrePositivity.KST.SConstruction.monicBoundaryKanSequenceProjection
#print axioms SerrePositivity.KST.SConstruction.monicBoundaryKanSequenceProjection
#check @SerrePositivity.KST.SConstruction.monicBoundaryKanSequenceProjection_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.monicBoundaryKanSequenceProjection_piIsomorphism
#check @SerrePositivity.KST.SConstruction.kKanSequenceLevel
#print axioms SerrePositivity.KST.SConstruction.kKanSequenceLevel
#check @SerrePositivity.KST.SConstruction.kKanSequenceSigma
#print axioms SerrePositivity.KST.SConstruction.kKanSequenceSigma
#check @SerrePositivity.KST.SConstruction.kKanSequence
#print axioms SerrePositivity.KST.SConstruction.kKanSequence
#check @SerrePositivity.KST.SConstruction.kKanSequence_zero_adjoint
#print axioms SerrePositivity.KST.SConstruction.kKanSequence_zero_adjoint
#check @SerrePositivity.KST.SConstruction.kKanSequence_zero_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.kKanSequence_zero_piIsomorphism
#check @SerrePositivity.KST.SConstruction.monicKKanSequence
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequence
#check @SerrePositivity.KST.SConstruction.monicKKanSequence_sigma_mono
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequence_sigma_mono
#check @SerrePositivity.KST.SConstruction.monicKKanSequenceProjection
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequenceProjection
#check @SerrePositivity.KST.SConstruction.monicKKanSequenceProjection_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequenceProjection_piIsomorphism
#check @SerrePositivity.KST.SConstruction.monicKKanSequence_zero
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequence_zero

-- 反復 S の構造射の成分での自然性と単射置換した列間の射
#check @SerrePositivity.KST.SConstruction.pointedComponentInverse_naturality
#print axioms SerrePositivity.KST.SConstruction.pointedComponentInverse_naturality
#check @SerrePositivity.KST.SConstruction.oneDirectionKanComparisonInverse_naturality_component
#print axioms SerrePositivity.KST.SConstruction.oneDirectionKanComparisonInverse_naturality_component
#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblyAdjoint_naturality_component
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblyAdjoint_naturality_component
#check @SerrePositivity.KST.SConstruction.pointedComponentUncurry
#print axioms SerrePositivity.KST.SConstruction.pointedComponentUncurry
#check @SerrePositivity.KST.SConstruction.boundaryKanAssemblySigma_naturality_component
#print axioms SerrePositivity.KST.SConstruction.boundaryKanAssemblySigma_naturality_component
#check @SerrePositivity.KST.SConstruction.pointedLoopCounit_naturality
#print axioms SerrePositivity.KST.SConstruction.pointedLoopCounit_naturality
#check @SerrePositivity.KST.SConstruction.kKanSequenceLevelMap
#print axioms SerrePositivity.KST.SConstruction.kKanSequenceLevelMap
#check @SerrePositivity.KST.SConstruction.kKanSequenceLevelMap_comm
#print axioms SerrePositivity.KST.SConstruction.kKanSequenceLevelMap_comm
#check @SerrePositivity.KST.SConstruction.monicKToRawLevelMap
#print axioms SerrePositivity.KST.SConstruction.monicKToRawLevelMap
#check @SerrePositivity.KST.SConstruction.pointedComponent_sequence_precompose
#print axioms SerrePositivity.KST.SConstruction.pointedComponent_sequence_precompose
#check @SerrePositivity.KST.SConstruction.monicKToRawLevelMap_comm
#print axioms SerrePositivity.KST.SConstruction.monicKToRawLevelMap_comm
#check @SerrePositivity.KST.SConstruction.monicKToRawMap
#print axioms SerrePositivity.KST.SConstruction.monicKToRawMap
#check @SerrePositivity.KST.SConstruction.monicKToRawMap_component
#print axioms SerrePositivity.KST.SConstruction.monicKToRawMap_component
#check @SerrePositivity.KST.SConstruction.monicKKanSequenceProjection_rlp
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequenceProjection_rlp
#check @SerrePositivity.KST.SConstruction.monicKKanSequenceMap
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequenceMap
#check @SerrePositivity.KST.SConstruction.monicKKanSequenceMap_projection
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequenceMap_projection
#check @SerrePositivity.KST.SConstruction.monicKKanSequenceMap_projection_component
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequenceMap_projection_component

-- 候補列の射の成分での関手法則と段ごとの π の自然同型
#check @SerrePositivity.KST.SConstruction.pointedComponent_cancel_right_of_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.pointedComponent_cancel_right_of_piIsomorphism
#check @SerrePositivity.KST.SConstruction.kKanSequenceLevelMap_id
#print axioms SerrePositivity.KST.SConstruction.kKanSequenceLevelMap_id
#check @SerrePositivity.KST.SConstruction.kKanSequenceLevelMap_comp
#print axioms SerrePositivity.KST.SConstruction.kKanSequenceLevelMap_comp
#check @SerrePositivity.KST.SConstruction.monicKKanSequenceMap_id_component
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequenceMap_id_component
#check @SerrePositivity.KST.SConstruction.monicKKanSequenceMap_comp_component
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequenceMap_comp_component
#check @SerrePositivity.KST.SConstruction.pointedHomotopyMap_eq_of_component
#print axioms SerrePositivity.KST.SConstruction.pointedHomotopyMap_eq_of_component
#check @SerrePositivity.KST.SConstruction.kStageHomotopyFunctor
#print axioms SerrePositivity.KST.SConstruction.kStageHomotopyFunctor
#check @SerrePositivity.KST.SConstruction.rawKStageHomotopyFunctor
#print axioms SerrePositivity.KST.SConstruction.rawKStageHomotopyFunctor
#check @SerrePositivity.KST.SConstruction.kStageHomotopyProjection
#print axioms SerrePositivity.KST.SConstruction.kStageHomotopyProjection
#check @SerrePositivity.KST.SConstruction.kStageHomotopyProjection_app_isIso
#print axioms SerrePositivity.KST.SConstruction.kStageHomotopyProjection_app_isIso
#check @SerrePositivity.KST.SConstruction.kStageHomotopyIso
#print axioms SerrePositivity.KST.SConstruction.kStageHomotopyIso

-- 全ての正の反復段の連結性
#check @SerrePositivity.KST.SConstruction.multiDiagonalCoreSConstruction_isConnected
#print axioms SerrePositivity.KST.SConstruction.multiDiagonalCoreSConstruction_isConnected
#check @SerrePositivity.KST.SConstruction.boundaryReductionQuotient_piZero_bijective
#print axioms SerrePositivity.KST.SConstruction.boundaryReductionQuotient_piZero_bijective
#check @SerrePositivity.KST.SConstruction.boundaryReducedRealization_isConnected
#print axioms SerrePositivity.KST.SConstruction.boundaryReducedRealization_isConnected
#check @SerrePositivity.KST.SConstruction.boundaryKanRealization_isConnected
#print axioms SerrePositivity.KST.SConstruction.boundaryKanRealization_isConnected
#check @SerrePositivity.KST.SConstruction.pointedIsConnected_of_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.pointedIsConnected_of_piIsomorphism
#check @SerrePositivity.KST.SConstruction.kKanSequence_positive_isConnected
#print axioms SerrePositivity.KST.SConstruction.kKanSequence_positive_isConnected
#check @SerrePositivity.KST.SConstruction.monicKKanSequence_positive_isConnected
#print axioms SerrePositivity.KST.SConstruction.monicKKanSequence_positive_isConnected

-- 単体的経路構成・実際の収縮・S の経路実現の弱可縮性
#check @SerrePositivity.KST.SConstruction.simplicialPathVertex
#print axioms SerrePositivity.KST.SConstruction.simplicialPathVertex
#check @SerrePositivity.KST.SConstruction.simplicialPathVertex_zero
#print axioms SerrePositivity.KST.SConstruction.simplicialPathVertex_zero
#check @SerrePositivity.KST.SConstruction.simplicialPathVertex_naturality
#print axioms SerrePositivity.KST.SConstruction.simplicialPathVertex_naturality
#check @SerrePositivity.KST.SConstruction.simplicialPath
#print axioms SerrePositivity.KST.SConstruction.simplicialPath
#check @SerrePositivity.KST.SConstruction.simplicialPathAugmentation
#print axioms SerrePositivity.KST.SConstruction.simplicialPathAugmentation
#check @SerrePositivity.KST.SConstruction.augmentedSimplicialPath
#print axioms SerrePositivity.KST.SConstruction.augmentedSimplicialPath
#check @SerrePositivity.KST.SConstruction.simplicialPathExtraDegeneracy
#print axioms SerrePositivity.KST.SConstruction.simplicialPathExtraDegeneracy
#check @SerrePositivity.KST.SConstruction.simplicialPathCut
#print axioms SerrePositivity.KST.SConstruction.simplicialPathCut
#check @SerrePositivity.KST.SConstruction.simplicialPathCut_naturality
#print axioms SerrePositivity.KST.SConstruction.simplicialPathCut_naturality
#check @SerrePositivity.KST.SConstruction.simplicialPathCut_zero
#print axioms SerrePositivity.KST.SConstruction.simplicialPathCut_zero
#check @SerrePositivity.KST.SConstruction.simplicialPathCut_one
#print axioms SerrePositivity.KST.SConstruction.simplicialPathCut_one
#check @SerrePositivity.KST.SConstruction.simplicialPathSection
#print axioms SerrePositivity.KST.SConstruction.simplicialPathSection
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalProjection
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalProjection
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalSection
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalSection
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalCylinder
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalCylinder
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalSection_projection
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalSection_projection
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalCylinder_zero
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalCylinder_zero
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalCylinder_one
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalCylinder_one
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalContraction
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalContraction
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalProjection_image_isIso
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalProjection_image_isIso
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonal_toPoint_image_isIso
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonal_toPoint_image_isIso
#check @SerrePositivity.KST.SConstruction.sPathRealization
#print axioms SerrePositivity.KST.SConstruction.sPathRealization
#check @SerrePositivity.KST.SConstruction.sPathRealizationProjection
#print axioms SerrePositivity.KST.SConstruction.sPathRealizationProjection
#check @SerrePositivity.KST.SConstruction.sPathRealization_toPoint_image_isIso
#print axioms SerrePositivity.KST.SConstruction.sPathRealization_toPoint_image_isIso
#check @SerrePositivity.KST.SConstruction.simplicialPathTail
#print axioms SerrePositivity.KST.SConstruction.simplicialPathTail
#check @SerrePositivity.KST.SConstruction.simplicialPathTail_naturality
#print axioms SerrePositivity.KST.SConstruction.simplicialPathTail_naturality
#check @SerrePositivity.KST.SConstruction.simplicialPathBoundary
#print axioms SerrePositivity.KST.SConstruction.simplicialPathBoundary
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalBoundary
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalBoundary
#check @SerrePositivity.KST.SConstruction.sPathRealizationBoundary
#print axioms SerrePositivity.KST.SConstruction.sPathRealizationBoundary

-- 経路の第一行制限の全単体的自然性・対角比較・S₁ の照合
#check @SerrePositivity.KST.SConstruction.pathFirstRowOrderMap
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowOrderMap
#check @SerrePositivity.KST.SConstruction.pathFirstRowNerveFunctor
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowNerveFunctor
#check @SerrePositivity.KST.SConstruction.pathFirstRowSimplexNatIso
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowSimplexNatIso
#check @SerrePositivity.KST.SConstruction.pathFirstRowInclusion_naturality
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowInclusion_naturality
#check @SerrePositivity.KST.SConstruction.pathFirstRowDiagram
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowDiagram
#check @SerrePositivity.KST.SConstruction.pathFirstRowDiagram_obj_quasicategory
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowDiagram_obj_quasicategory
#check @SerrePositivity.KST.SConstruction.pathFirstRowRestriction
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowRestriction
#check @SerrePositivity.KST.SConstruction.pathFirstRowRestriction_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowRestriction_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.corePathFirstRowRestriction
#print axioms SerrePositivity.KST.SConstruction.corePathFirstRowRestriction
#check @SerrePositivity.KST.SConstruction.corePathFirstRowRestriction_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.corePathFirstRowRestriction_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.pathFirstRowDiagonalComparison
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowDiagonalComparison
#check @SerrePositivity.KST.SConstruction.pathFirstRowDiagonalComparison_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowDiagonalComparison_localized_isIso
#check @SerrePositivity.KST.SConstruction.pathFirstRowDiagramMap
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowDiagramMap
#check @SerrePositivity.KST.SConstruction.pathSConstructionMap
#print axioms SerrePositivity.KST.SConstruction.pathSConstructionMap
#check @SerrePositivity.KST.SConstruction.pathFirstRowRestriction_naturality
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowRestriction_naturality
#check @SerrePositivity.KST.SConstruction.pathFirstRowRestriction_zero
#print axioms SerrePositivity.KST.SConstruction.pathFirstRowRestriction_zero
#check @SerrePositivity.KST.SConstruction.corePathFirstRowRestriction_zero
#print axioms SerrePositivity.KST.SConstruction.corePathFirstRowRestriction_zero

-- S と有限反復 S による trivial Kan fibration の保存
#check @SerrePositivity.KST.SConstruction.ihomMap_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.ihomMap_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.fullSubcomplex_trivialKanFibration_of_reflects
#print axioms SerrePositivity.KST.SConstruction.fullSubcomplex_trivialKanFibration_of_reflects
#check @SerrePositivity.KST.SConstruction.isGapped_iff_postcomp_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.isGapped_iff_postcomp_of_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.multiSEndofunctor_map_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.multiSEndofunctor_map_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.multiCoreSConstructionFunctor_map_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.multiCoreSConstructionFunctor_map_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.multiRealizationFunctor_map_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.multiRealizationFunctor_map_localized_isIso

-- 経路の第一行比較の安定な入力への束ね・有限反復・弱可縮性
#check @SerrePositivity.KST.SConstruction.stableSPathDiagram
#print axioms SerrePositivity.KST.SConstruction.stableSPathDiagram
#check @SerrePositivity.KST.SConstruction.stablePathFirstRowDiagram
#print axioms SerrePositivity.KST.SConstruction.stablePathFirstRowDiagram
#check @SerrePositivity.KST.SConstruction.stablePathFirstRowRestriction
#print axioms SerrePositivity.KST.SConstruction.stablePathFirstRowRestriction
#check @SerrePositivity.KST.SConstruction.stablePathFirstRowRestriction_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.stablePathFirstRowRestriction_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.stablePathFirstRowRestriction_forget
#print axioms SerrePositivity.KST.SConstruction.stablePathFirstRowRestriction_forget
#check @SerrePositivity.KST.SConstruction.stablePathFirstRowZeroComparison
#print axioms SerrePositivity.KST.SConstruction.stablePathFirstRowZeroComparison
#check @SerrePositivity.KST.SConstruction.stablePathFirstRowRestriction_zero
#print axioms SerrePositivity.KST.SConstruction.stablePathFirstRowRestriction_zero
#check @SerrePositivity.KST.SConstruction.iteratedPathRealizationDiagram
#print axioms SerrePositivity.KST.SConstruction.iteratedPathRealizationDiagram
#check @SerrePositivity.KST.SConstruction.iteratedFirstRowRealizationDiagram
#print axioms SerrePositivity.KST.SConstruction.iteratedFirstRowRealizationDiagram
#check @SerrePositivity.KST.SConstruction.iteratedPathFirstRowComparison
#print axioms SerrePositivity.KST.SConstruction.iteratedPathFirstRowComparison
#check @SerrePositivity.KST.SConstruction.iteratedPathFirstRowComparison_app_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.iteratedPathFirstRowComparison_app_localized_isIso
#check @SerrePositivity.KST.SConstruction.iteratedPathRealization
#print axioms SerrePositivity.KST.SConstruction.iteratedPathRealization
#check @SerrePositivity.KST.SConstruction.iteratedFirstRowRealization
#print axioms SerrePositivity.KST.SConstruction.iteratedFirstRowRealization
#check @SerrePositivity.KST.SConstruction.iteratedPathFirstRowDiagonalComparison
#print axioms SerrePositivity.KST.SConstruction.iteratedPathFirstRowDiagonalComparison
#check @SerrePositivity.KST.SConstruction.iteratedPathFirstRowDiagonalComparison_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.iteratedPathFirstRowDiagonalComparison_localized_isIso
#check @SerrePositivity.KST.SConstruction.iteratedPathFirstRowComparison_zero
#print axioms SerrePositivity.KST.SConstruction.iteratedPathFirstRowComparison_zero
#check @SerrePositivity.KST.SConstruction.multiSConstruction_isContractibleKan_of_contractible
#print axioms SerrePositivity.KST.SConstruction.multiSConstruction_isContractibleKan_of_contractible
#check @SerrePositivity.KST.SConstruction.multiCoreSConstruction_isContractibleKan_of_contractible
#print axioms SerrePositivity.KST.SConstruction.multiCoreSConstruction_isContractibleKan_of_contractible
#check @SerrePositivity.KST.SConstruction.multiRealization_toPoint_localized_isIso_of_contractible
#print axioms SerrePositivity.KST.SConstruction.multiRealization_toPoint_localized_isIso_of_contractible
#check @SerrePositivity.KST.SConstruction.iteratedPathRealization_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.iteratedPathRealization_toPoint_localized_isIso
#check @SerrePositivity.KST.SConstruction.iteratedFirstRowRealization_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.iteratedFirstRowRealization_toPoint_localized_isIso

-- 反復した経路の境界図式と多重実現への全単体的座標同型
#check @SerrePositivity.KST.SConstruction.simplicialPathBoundary_naturality
#print axioms SerrePositivity.KST.SConstruction.simplicialPathBoundary_naturality
#check @SerrePositivity.KST.SConstruction.stableSConstructionDiagram
#print axioms SerrePositivity.KST.SConstruction.stableSConstructionDiagram
#check @SerrePositivity.KST.SConstruction.iteratedSRealizationDiagram
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealizationDiagram
#check @SerrePositivity.KST.SConstruction.iteratedPathBoundary
#print axioms SerrePositivity.KST.SConstruction.iteratedPathBoundary
#check @SerrePositivity.KST.SConstruction.iteratedSRealization
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealization
#check @SerrePositivity.KST.SConstruction.iteratedPathRealizationBoundary
#print axioms SerrePositivity.KST.SConstruction.iteratedPathRealizationBoundary
#check @SerrePositivity.KST.SConstruction.iteratedSRealizationDiagramMap
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealizationDiagramMap
#check @SerrePositivity.KST.SConstruction.iteratedPathRealizationDiagramMap
#print axioms SerrePositivity.KST.SConstruction.iteratedPathRealizationDiagramMap
#check @SerrePositivity.KST.SConstruction.iteratedPathBoundary_naturality
#print axioms SerrePositivity.KST.SConstruction.iteratedPathBoundary_naturality
#check @SerrePositivity.KST.SConstruction.iteratedSRealizationMap
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealizationMap
#check @SerrePositivity.KST.SConstruction.iteratedPathRealizationMap
#print axioms SerrePositivity.KST.SConstruction.iteratedPathRealizationMap
#check @SerrePositivity.KST.SConstruction.iteratedPathRealizationBoundary_naturality
#print axioms SerrePositivity.KST.SConstruction.iteratedPathRealizationBoundary_naturality
#check @SerrePositivity.KST.SConstruction.multiSConstruction_diagonal_inner
#print axioms SerrePositivity.KST.SConstruction.multiSConstruction_diagonal_inner
#check @SerrePositivity.KST.SConstruction.multiSEndofunctor_diagonal_inner_iso
#print axioms SerrePositivity.KST.SConstruction.multiSEndofunctor_diagonal_inner_iso
#check @SerrePositivity.KST.SConstruction.iteratedSRealization_zero
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealization_zero
#check @SerrePositivity.KST.SConstruction.iteratedPathRealization_zero
#print axioms SerrePositivity.KST.SConstruction.iteratedPathRealization_zero
#check @SerrePositivity.KST.SConstruction.iteratedPathRealizationBoundary_zero
#print axioms SerrePositivity.KST.SConstruction.iteratedPathRealizationBoundary_zero
#check @SerrePositivity.KST.SConstruction.diagonalSEndofunctor
#print axioms SerrePositivity.KST.SConstruction.diagonalSEndofunctor
#check @SerrePositivity.KST.SConstruction.diagonalSEndofunctor_zero
#print axioms SerrePositivity.KST.SConstruction.diagonalSEndofunctor_zero
#check @SerrePositivity.KST.SConstruction.diagonalSEndofunctor_succ
#print axioms SerrePositivity.KST.SConstruction.diagonalSEndofunctor_succ
#check @SerrePositivity.KST.SConstruction.diagonalSInnerComparisonNatIso
#print axioms SerrePositivity.KST.SConstruction.diagonalSInnerComparisonNatIso
#check @SerrePositivity.KST.SConstruction.stableEndofunctorCoreEvaluation
#print axioms SerrePositivity.KST.SConstruction.stableEndofunctorCoreEvaluation
#check @SerrePositivity.KST.SConstruction.diagonalInnerSCoreDiagram
#print axioms SerrePositivity.KST.SConstruction.diagonalInnerSCoreDiagram
#check @SerrePositivity.KST.SConstruction.diagonalInnerSCoreDiagramIso
#print axioms SerrePositivity.KST.SConstruction.diagonalInnerSCoreDiagramIso
#check @SerrePositivity.KST.SConstruction.diagonalInnerSRealizationIso
#print axioms SerrePositivity.KST.SConstruction.diagonalInnerSRealizationIso
#check @SerrePositivity.KST.SConstruction.iteratedSRealizationInnerIso
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealizationInnerIso
#check @SerrePositivity.KST.SConstruction.iteratedSRealizationCoordinateIso
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealizationCoordinateIso
#check @SerrePositivity.KST.SConstruction.canonicalIteratedPathBoundary
#print axioms SerrePositivity.KST.SConstruction.canonicalIteratedPathBoundary
#check @SerrePositivity.KST.SConstruction.reducedIteratedPathBoundary
#print axioms SerrePositivity.KST.SConstruction.reducedIteratedPathBoundary
#check @SerrePositivity.KST.SConstruction.kanIteratedPathBoundary
#print axioms SerrePositivity.KST.SConstruction.kanIteratedPathBoundary

-- 定数経路を潰す点つき反復経路・自然な境界・実際の可縮 Kan 性
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalSection_mono
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalSection_mono
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalSection_naturality
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalSection_naturality
#check @SerrePositivity.KST.SConstruction.reducedPathDiagonal
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonal
#check @SerrePositivity.KST.SConstruction.pathDiagonalReductionQuotient
#print axioms SerrePositivity.KST.SConstruction.pathDiagonalReductionQuotient
#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalMap
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalMap
#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalMap_quotient
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalMap_quotient
#check @SerrePositivity.KST.SConstruction.pathDiagonalReductionQuotient_image_isIso
#print axioms SerrePositivity.KST.SConstruction.pathDiagonalReductionQuotient_image_isIso
#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalFunctor
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalFunctor
#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalSection_boundary
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalSection_boundary
#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalBoundary
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalBoundary
#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalBoundary_quotient
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalBoundary_quotient
#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalBoundary_naturality
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalBoundary_naturality
#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalBoundaryNat
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalBoundaryNat
#check @SerrePositivity.KST.SConstruction.pointedIsContractibleKan_of_localized_toPoint
#print axioms SerrePositivity.KST.SConstruction.pointedIsContractibleKan_of_localized_toPoint
#check @SerrePositivity.KST.SConstruction.iteratedSRealizationDiagramFunctor
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealizationDiagramFunctor
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathFunctor
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathFunctor
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathRealization
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathRealization
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathQuotient
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathQuotient
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathQuotient_image_isIso
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathQuotient_image_isIso
#check @SerrePositivity.KST.SConstruction.pointedIteratedPath_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPath_toPoint_localized_isIso
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathBoundaryNat
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathBoundaryNat
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathBoundary
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathBoundary
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathBoundary_quotient
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathBoundary_quotient
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathKanFunctor
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathKanFunctor
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathKan_kanComplex
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathKan_kanComplex
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathKan_toPoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathKan_toPoint_localized_isIso
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathKan_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathKan_isContractibleKan
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathKanBoundaryNat
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathKanBoundaryNat
#check @SerrePositivity.KST.SConstruction.pointedIteratedPathKanBoundary
#print axioms SerrePositivity.KST.SConstruction.pointedIteratedPathKanBoundary

-- 最内側の可変次数と最後の零方向の座標比較
#check @SerrePositivity.KST.SConstruction.innerVariableIndex
#print axioms SerrePositivity.KST.SConstruction.innerVariableIndex
#check @SerrePositivity.KST.SConstruction.innerVariableSComparisonIso
#print axioms SerrePositivity.KST.SConstruction.innerVariableSComparisonIso
#check @SerrePositivity.KST.SConstruction.innerVariableSMap_succ
#print axioms SerrePositivity.KST.SConstruction.innerVariableSMap_succ
#check @SerrePositivity.KST.SConstruction.innerVariableSComparisonIso_naturality
#print axioms SerrePositivity.KST.SConstruction.innerVariableSComparisonIso_naturality
#check @SerrePositivity.KST.SConstruction.innerVariableIndex_obj_last
#print axioms SerrePositivity.KST.SConstruction.innerVariableIndex_obj_last
#check @SerrePositivity.KST.SConstruction.innerVariableIndex_obj_castSucc
#print axioms SerrePositivity.KST.SConstruction.innerVariableIndex_obj_castSucc
#check @SerrePositivity.KST.SConstruction.innerVariableIndex_map_last
#print axioms SerrePositivity.KST.SConstruction.innerVariableIndex_map_last
#check @SerrePositivity.KST.SConstruction.innerVariableIndex_map_castSucc
#print axioms SerrePositivity.KST.SConstruction.innerVariableIndex_map_castSucc
#check @SerrePositivity.KST.SConstruction.innerVariableSComparisonNatIso
#print axioms SerrePositivity.KST.SConstruction.innerVariableSComparisonNatIso
#check @SerrePositivity.KST.SConstruction.innerVariableIndex_obj_diagonal
#print axioms SerrePositivity.KST.SConstruction.innerVariableIndex_obj_diagonal
#check @SerrePositivity.KST.SConstruction.innerVariableIndex_obj_zero
#print axioms SerrePositivity.KST.SConstruction.innerVariableIndex_obj_zero
#check @SerrePositivity.KST.SConstruction.innerVariableIndex_zero_map
#print axioms SerrePositivity.KST.SConstruction.innerVariableIndex_zero_map

-- 最内側の零方向の包含の自然変換の比較
#check @SerrePositivity.KST.SConstruction.innerZeroDirectionComparisonIso
#print axioms SerrePositivity.KST.SConstruction.innerZeroDirectionComparisonIso
#check @SerrePositivity.KST.SConstruction.innerDiagonalComparisonIso
#print axioms SerrePositivity.KST.SConstruction.innerDiagonalComparisonIso
#check @SerrePositivity.KST.SConstruction.innerZeroDirectionComparisonIso_inclusion
#print axioms SerrePositivity.KST.SConstruction.innerZeroDirectionComparisonIso_inclusion

-- 内側の零列から全零境界商への自然な点つき比較と経路境界
#check @SerrePositivity.KST.SConstruction.diagonalSInnerComparisonNatIso_zero_app
#print axioms SerrePositivity.KST.SConstruction.diagonalSInnerComparisonNatIso_zero_app
#check @SerrePositivity.KST.SConstruction.diagonalSInnerComparisonNatIso_succ_app
#print axioms SerrePositivity.KST.SConstruction.diagonalSInnerComparisonNatIso_succ_app
#check @SerrePositivity.KST.SConstruction.diagonalSInnerComparisonNatIso_app_eq
#print axioms SerrePositivity.KST.SConstruction.diagonalSInnerComparisonNatIso_app_eq
#check @SerrePositivity.KST.SConstruction.innerDiagonalTransport_succ
#print axioms SerrePositivity.KST.SConstruction.innerDiagonalTransport_succ
#check @SerrePositivity.KST.SConstruction.innerDiagonalComparisonIso_zero_app
#print axioms SerrePositivity.KST.SConstruction.innerDiagonalComparisonIso_zero_app
#check @SerrePositivity.KST.SConstruction.innerDiagonalComparisonIso_succ_app
#print axioms SerrePositivity.KST.SConstruction.innerDiagonalComparisonIso_succ_app
#check @SerrePositivity.KST.SConstruction.innerDiagonalComparisonIso_hom_eq
#print axioms SerrePositivity.KST.SConstruction.innerDiagonalComparisonIso_hom_eq
#check @SerrePositivity.KST.SConstruction.diagonalSInnerComparisonNatIso_app_eq_inner
#print axioms SerrePositivity.KST.SConstruction.diagonalSInnerComparisonNatIso_app_eq_inner
#check @SerrePositivity.KST.SConstruction.iteratedZeroColumnLastZeroPreimage
#print axioms SerrePositivity.KST.SConstruction.iteratedZeroColumnLastZeroPreimage
#check @SerrePositivity.KST.SConstruction.iteratedZeroColumnLastZeroPreimage_fac
#print axioms SerrePositivity.KST.SConstruction.iteratedZeroColumnLastZeroPreimage_fac
#check @SerrePositivity.KST.SConstruction.iteratedZeroColumn_range_le_fatBoundary
#print axioms SerrePositivity.KST.SConstruction.iteratedZeroColumn_range_le_fatBoundary
#check @SerrePositivity.KST.SConstruction.iteratedZeroColumnFatBoundaryLift
#print axioms SerrePositivity.KST.SConstruction.iteratedZeroColumnFatBoundaryLift
#check @SerrePositivity.KST.SConstruction.iteratedZeroColumnFatBoundaryLift_ι
#print axioms SerrePositivity.KST.SConstruction.iteratedZeroColumnFatBoundaryLift_ι
#check @SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparison
#print axioms SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparison
#check @SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparison_quotient
#print axioms SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparison_quotient
#check @SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparison_image_isIso
#print axioms SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparison_image_isIso
#check @SerrePositivity.KST.SConstruction.iteratedSRealizationCoordinateIso_naturality
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealizationCoordinateIso_naturality
#check @SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparison_naturality
#print axioms SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparison_naturality
#check @SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparisonNat
#print axioms SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparisonNat
#check @SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparisonKanNat
#print axioms SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparisonKanNat
#check @SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparisonKan_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.innerZeroToFullBoundaryComparisonKan_piIsomorphism
#check @SerrePositivity.KST.SConstruction.pointedFullIteratedPathBoundaryNat
#print axioms SerrePositivity.KST.SConstruction.pointedFullIteratedPathBoundaryNat
#check @SerrePositivity.KST.SConstruction.pointedFullIteratedPathBoundary
#print axioms SerrePositivity.KST.SConstruction.pointedFullIteratedPathBoundary
#check @SerrePositivity.KST.SConstruction.pointedFullIteratedPathBoundary_quotient
#print axioms SerrePositivity.KST.SConstruction.pointedFullIteratedPathBoundary_quotient
#check @SerrePositivity.KST.SConstruction.pointedFullIteratedPathKanBoundaryNat
#print axioms SerrePositivity.KST.SConstruction.pointedFullIteratedPathKanBoundaryNat
#check @SerrePositivity.KST.SConstruction.pointedFullIteratedPathKanBoundary
#print axioms SerrePositivity.KST.SConstruction.pointedFullIteratedPathKanBoundary
#check @SerrePositivity.KST.SConstruction.pointedFullIteratedPathKanBoundary_quotient
#print axioms SerrePositivity.KST.SConstruction.pointedFullIteratedPathKanBoundary_quotient

-- 反復経路境界の path homotopy fiber と loop の自然な比較
#check @SerrePositivity.KST.SConstruction.fiberTerminalInclusion_isIso
#print axioms SerrePositivity.KST.SConstruction.fiberTerminalInclusion_isIso
#check @SerrePositivity.KST.SConstruction.fiberInclusion_piIsomorphism_of_contractible_base
#print axioms SerrePositivity.KST.SConstruction.fiberInclusion_piIsomorphism_of_contractible_base
#check @SerrePositivity.KST.SConstruction.pointedPullbackFiberTo
#print axioms SerrePositivity.KST.SConstruction.pointedPullbackFiberTo
#check @SerrePositivity.KST.SConstruction.pointedPullbackFiberTo_ι
#print axioms SerrePositivity.KST.SConstruction.pointedPullbackFiberTo_ι
#check @SerrePositivity.KST.SConstruction.pointedPullbackFiberFrom
#print axioms SerrePositivity.KST.SConstruction.pointedPullbackFiberFrom
#check @SerrePositivity.KST.SConstruction.pointedPullbackFiberFrom_ι
#print axioms SerrePositivity.KST.SConstruction.pointedPullbackFiberFrom_ι
#check @SerrePositivity.KST.SConstruction.pointedPullbackFiberIso
#print axioms SerrePositivity.KST.SConstruction.pointedPullbackFiberIso
#check @SerrePositivity.KST.SConstruction.pathHomotopyFiber
#print axioms SerrePositivity.KST.SConstruction.pathHomotopyFiber
#check @SerrePositivity.KST.SConstruction.pathHomotopyFiberProjection
#print axioms SerrePositivity.KST.SConstruction.pathHomotopyFiberProjection
#check @SerrePositivity.KST.SConstruction.pathHomotopyFiberProjection_fibration
#print axioms SerrePositivity.KST.SConstruction.pathHomotopyFiberProjection_fibration
#check @SerrePositivity.KST.SConstruction.pathHomotopyFiber_kanComplex
#print axioms SerrePositivity.KST.SConstruction.pathHomotopyFiber_kanComplex
#check @SerrePositivity.KST.SConstruction.loopPointedPathFiberIso
#print axioms SerrePositivity.KST.SConstruction.loopPointedPathFiberIso
#check @SerrePositivity.KST.SConstruction.loopToPathHomotopyFiber
#print axioms SerrePositivity.KST.SConstruction.loopToPathHomotopyFiber
#check @SerrePositivity.KST.SConstruction.loopToPathHomotopyFiber_projection
#print axioms SerrePositivity.KST.SConstruction.loopToPathHomotopyFiber_projection
#check @SerrePositivity.KST.SConstruction.loopToPathHomotopyFiber_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.loopToPathHomotopyFiber_piIsomorphism
#check @SerrePositivity.KST.SConstruction.loopPointedPathFiberIso_hom_ι
#print axioms SerrePositivity.KST.SConstruction.loopPointedPathFiberIso_hom_ι
#check @SerrePositivity.KST.SConstruction.loopToPathHomotopyFiber_path
#print axioms SerrePositivity.KST.SConstruction.loopToPathHomotopyFiber_path
#check @SerrePositivity.KST.SConstruction.pathHomotopyFiberMap
#print axioms SerrePositivity.KST.SConstruction.pathHomotopyFiberMap
#check @SerrePositivity.KST.SConstruction.pathHomotopyFiberMap_path
#print axioms SerrePositivity.KST.SConstruction.pathHomotopyFiberMap_path
#check @SerrePositivity.KST.SConstruction.pathHomotopyFiberMap_projection
#print axioms SerrePositivity.KST.SConstruction.pathHomotopyFiberMap_projection
#check @SerrePositivity.KST.SConstruction.loopToPathHomotopyFiber_naturality
#print axioms SerrePositivity.KST.SConstruction.loopToPathHomotopyFiber_naturality
#check @SerrePositivity.KST.SConstruction.pathHomotopyFiberMap_id
#print axioms SerrePositivity.KST.SConstruction.pathHomotopyFiberMap_id
#check @SerrePositivity.KST.SConstruction.pathHomotopyFiberMap_comp
#print axioms SerrePositivity.KST.SConstruction.pathHomotopyFiberMap_comp
#check @SerrePositivity.KST.SConstruction.pathHomotopyFiberFunctorOfNat
#print axioms SerrePositivity.KST.SConstruction.pathHomotopyFiberFunctorOfNat
#check @SerrePositivity.KST.SConstruction.loopToPathHomotopyFiberNat
#print axioms SerrePositivity.KST.SConstruction.loopToPathHomotopyFiberNat
#check @SerrePositivity.KST.SConstruction.iteratedPathHomotopyFiber
#print axioms SerrePositivity.KST.SConstruction.iteratedPathHomotopyFiber
#check @SerrePositivity.KST.SConstruction.iteratedPathHomotopyFiber_kanComplex
#print axioms SerrePositivity.KST.SConstruction.iteratedPathHomotopyFiber_kanComplex
#check @SerrePositivity.KST.SConstruction.iteratedPathHomotopyFiberMap
#print axioms SerrePositivity.KST.SConstruction.iteratedPathHomotopyFiberMap
#check @SerrePositivity.KST.SConstruction.iteratedPathHomotopyFiberFunctor
#print axioms SerrePositivity.KST.SConstruction.iteratedPathHomotopyFiberFunctor
#check @SerrePositivity.KST.SConstruction.iteratedPathLoopComparison
#print axioms SerrePositivity.KST.SConstruction.iteratedPathLoopComparison
#check @SerrePositivity.KST.SConstruction.iteratedPathLoopComparison_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.iteratedPathLoopComparison_piIsomorphism
#check @SerrePositivity.KST.SConstruction.iteratedPathLoopComparisonNat
#print axioms SerrePositivity.KST.SConstruction.iteratedPathLoopComparisonNat

-- McCarthy 法の全 gapped object 単体集合と加法性の比較射
#check @SerrePositivity.KST.SConstruction.diagonalObjects
#print axioms SerrePositivity.KST.SConstruction.diagonalObjects
#check @SerrePositivity.KST.SConstruction.diagonalObjectInclusion
#print axioms SerrePositivity.KST.SConstruction.diagonalObjectInclusion
#check @SerrePositivity.KST.SConstruction.diagonalObjectInclusionNat
#print axioms SerrePositivity.KST.SConstruction.diagonalObjectInclusionNat
#check @SerrePositivity.KST.SConstruction.objectSConstruction
#print axioms SerrePositivity.KST.SConstruction.objectSConstruction
#check @SerrePositivity.KST.SConstruction.objectSConstruction_obj
#print axioms SerrePositivity.KST.SConstruction.objectSConstruction_obj
#check @SerrePositivity.KST.SConstruction.coreVertexNatIso
#print axioms SerrePositivity.KST.SConstruction.coreVertexNatIso
#check @SerrePositivity.KST.SConstruction.coreDiagramObjectsIso
#print axioms SerrePositivity.KST.SConstruction.coreDiagramObjectsIso
#check @SerrePositivity.KST.SConstruction.objectCoreDiagonalComparisonNat
#print axioms SerrePositivity.KST.SConstruction.objectCoreDiagonalComparisonNat
#check @SerrePositivity.KST.SConstruction.objectSCoreVertexIso
#print axioms SerrePositivity.KST.SConstruction.objectSCoreVertexIso
#check @SerrePositivity.KST.SConstruction.objectToCoreSRealization
#print axioms SerrePositivity.KST.SConstruction.objectToCoreSRealization
#check @SerrePositivity.KST.SConstruction.objectToCoreSRealization_eq
#print axioms SerrePositivity.KST.SConstruction.objectToCoreSRealization_eq
#check @SerrePositivity.KST.SConstruction.objectToCoreSRealization_naturality
#print axioms SerrePositivity.KST.SConstruction.objectToCoreSRealization_naturality
#check @SerrePositivity.KST.SConstruction.objectSConstructionFunctor
#print axioms SerrePositivity.KST.SConstruction.objectSConstructionFunctor
#check @SerrePositivity.KST.SConstruction.objectSConstructionFunctor_obj
#print axioms SerrePositivity.KST.SConstruction.objectSConstructionFunctor_obj
#check @SerrePositivity.KST.SConstruction.sTwoFaceComparisonNat
#print axioms SerrePositivity.KST.SConstruction.sTwoFaceComparisonNat
#check @SerrePositivity.KST.SConstruction.sTwoSubobject
#print axioms SerrePositivity.KST.SConstruction.sTwoSubobject
#check @SerrePositivity.KST.SConstruction.sTwoMiddle
#print axioms SerrePositivity.KST.SConstruction.sTwoMiddle
#check @SerrePositivity.KST.SConstruction.sTwoQuotient
#print axioms SerrePositivity.KST.SConstruction.sTwoQuotient
#check @SerrePositivity.KST.SConstruction.sTwoAdditivityComparisonNat
#print axioms SerrePositivity.KST.SConstruction.sTwoAdditivityComparisonNat
#check @SerrePositivity.KST.SConstruction.sTwoAdditivityComparisonNat_fst
#print axioms SerrePositivity.KST.SConstruction.sTwoAdditivityComparisonNat_fst
#check @SerrePositivity.KST.SConstruction.sTwoAdditivityComparisonNat_snd
#print axioms SerrePositivity.KST.SConstruction.sTwoAdditivityComparisonNat_snd
#check @SerrePositivity.KST.SConstruction.objectSAdditivityComparisonNat
#print axioms SerrePositivity.KST.SConstruction.objectSAdditivityComparisonNat
#check @SerrePositivity.KST.SConstruction.coreSAdditivityComparisonNat
#print axioms SerrePositivity.KST.SConstruction.coreSAdditivityComparisonNat

#check @SerrePositivity.KST.SConstruction.exists_stable_pushoutPresentation_of_span
#print axioms SerrePositivity.KST.SConstruction.exists_stable_pushoutPresentation_of_span
#check @SerrePositivity.KST.SConstruction.exists_stable_pushoutSquare_of_span
#print axioms SerrePositivity.KST.SConstruction.exists_stable_pushoutSquare_of_span
#check @SerrePositivity.KST.SConstruction.stable_hasColimit_span
#print axioms SerrePositivity.KST.SConstruction.stable_hasColimit_span
#check @SerrePositivity.KST.SConstruction.stable_pushoutProjection_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.stable_pushoutProjection_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.exists_relative_stable_pushoutFamily
#print axioms SerrePositivity.KST.SConstruction.exists_relative_stable_pushoutFamily
#check @SerrePositivity.KST.SConstruction.exists_stablePushoutSection_extending
#print axioms SerrePositivity.KST.SConstruction.exists_stablePushoutSection_extending
#check @SerrePositivity.KST.SConstruction.stablePushoutFamilySpace
#print axioms SerrePositivity.KST.SConstruction.stablePushoutFamilySpace
#check @SerrePositivity.KST.SConstruction.stablePushoutFamilySpace_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.stablePushoutFamilySpace_isContractibleKan
#check @SerrePositivity.KST.SConstruction.stablePushoutFamiliesIso
#print axioms SerrePositivity.KST.SConstruction.stablePushoutFamiliesIso
#check @SerrePositivity.KST.SConstruction.stablePushoutSection
#print axioms SerrePositivity.KST.SConstruction.stablePushoutSection
#check @SerrePositivity.KST.SConstruction.stablePushoutSection_projection
#print axioms SerrePositivity.KST.SConstruction.stablePushoutSection_projection
#check @SerrePositivity.KST.SConstruction.stablePushoutFunctor
#print axioms SerrePositivity.KST.SConstruction.stablePushoutFunctor
#check @SerrePositivity.KST.SConstruction.PreservesCofiberData.isPushoutSquare
#print axioms SerrePositivity.KST.SConstruction.PreservesCofiberData.isPushoutSquare
#check @SerrePositivity.KST.SConstruction.PreservesCofiberData.toSConstructionData
#print axioms SerrePositivity.KST.SConstruction.PreservesCofiberData.toSConstructionData
#check @SerrePositivity.KST.SConstruction.preservesSConstructionData_iff_cofiberData
#print axioms SerrePositivity.KST.SConstruction.preservesSConstructionData_iff_cofiberData
#check @SerrePositivity.KST.SConstruction.stableModelHom_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.stableModelHom_preservesSConstructionData
#check @SerrePositivity.KST.SConstruction.functor_span_hasPointwiseColimits
#print axioms SerrePositivity.KST.SConstruction.functor_span_hasPointwiseColimits
#check @SerrePositivity.KST.SConstruction.functor_pushout_iff_pointwise
#print axioms SerrePositivity.KST.SConstruction.functor_pushout_iff_pointwise
#check @SerrePositivity.KST.SConstruction.gappedInclusion_pushout_iff
#print axioms SerrePositivity.KST.SConstruction.gappedInclusion_pushout_iff
#check @SerrePositivity.KST.SConstruction.gappedInclusion_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.gappedInclusion_preservesSConstructionData
#check @SerrePositivity.KST.SConstruction.gappedInclusion_pushout_iff_pointwise
#print axioms SerrePositivity.KST.SConstruction.gappedInclusion_pushout_iff_pointwise
#check @SerrePositivity.KST.SConstruction.pushoutDiagramsPostcomp
#print axioms SerrePositivity.KST.SConstruction.pushoutDiagramsPostcomp
#check @SerrePositivity.KST.SConstruction.pushoutDiagramsPostcomp_ι
#print axioms SerrePositivity.KST.SConstruction.pushoutDiagramsPostcomp_ι
#check @SerrePositivity.KST.SConstruction.pushoutDiagramsPostcomp_projection
#print axioms SerrePositivity.KST.SConstruction.pushoutDiagramsPostcomp_projection
#check @SerrePositivity.KST.SConstruction.stablePushoutSection_postcompIso
#print axioms SerrePositivity.KST.SConstruction.stablePushoutSection_postcompIso

#check @SerrePositivity.KST.SConstruction.identityPushoutShape
#print axioms SerrePositivity.KST.SConstruction.identityPushoutShape
#check @SerrePositivity.KST.SConstruction.identityPushoutShape_isPushout
#print axioms SerrePositivity.KST.SConstruction.identityPushoutShape_isPushout
#check @SerrePositivity.KST.SConstruction.identitySpanShape
#print axioms SerrePositivity.KST.SConstruction.identitySpanShape
#check @SerrePositivity.KST.SConstruction.identitySpanSection
#print axioms SerrePositivity.KST.SConstruction.identitySpanSection
#check @SerrePositivity.KST.SConstruction.identitySpanSection_shape
#print axioms SerrePositivity.KST.SConstruction.identitySpanSection_shape
#check @SerrePositivity.KST.SConstruction.identitySpanFamily
#print axioms SerrePositivity.KST.SConstruction.identitySpanFamily
#check @SerrePositivity.KST.SConstruction.identitySpanFamily_mono
#print axioms SerrePositivity.KST.SConstruction.identitySpanFamily_mono
#check @SerrePositivity.KST.SConstruction.identityPushoutFamily
#print axioms SerrePositivity.KST.SConstruction.identityPushoutFamily
#check @SerrePositivity.KST.SConstruction.identityPushoutFamily_ι
#print axioms SerrePositivity.KST.SConstruction.identityPushoutFamily_ι
#check @SerrePositivity.KST.SConstruction.identityPushoutFamily_projection
#print axioms SerrePositivity.KST.SConstruction.identityPushoutFamily_projection
#check @SerrePositivity.KST.SConstruction.identitySquareReconstruction
#print axioms SerrePositivity.KST.SConstruction.identitySquareReconstruction
#check @SerrePositivity.KST.SConstruction.identitySpanFamily_reconstruction
#print axioms SerrePositivity.KST.SConstruction.identitySpanFamily_reconstruction
#check @SerrePositivity.KST.SConstruction.identitySquareReconstruction_cross
#print axioms SerrePositivity.KST.SConstruction.identitySquareReconstruction_cross
#check @SerrePositivity.KST.SConstruction.identitySquareReconstruction_overlap
#print axioms SerrePositivity.KST.SConstruction.identitySquareReconstruction_overlap
#check @SerrePositivity.KST.SConstruction.subcomplexUnionMap
#print axioms SerrePositivity.KST.SConstruction.subcomplexUnionMap
#check @SerrePositivity.KST.SConstruction.identitySpanSubcomplex
#print axioms SerrePositivity.KST.SConstruction.identitySpanSubcomplex
#check @SerrePositivity.KST.SConstruction.identityUnionSquare
#print axioms SerrePositivity.KST.SConstruction.identityUnionSquare
#check @SerrePositivity.KST.SConstruction.identityUnionSquare_on_family
#print axioms SerrePositivity.KST.SConstruction.identityUnionSquare_on_family
#check @SerrePositivity.KST.SConstruction.identityUnionSquare_span
#print axioms SerrePositivity.KST.SConstruction.identityUnionSquare_span
#check @SerrePositivity.KST.SConstruction.identityUnionPushoutFamily
#print axioms SerrePositivity.KST.SConstruction.identityUnionPushoutFamily
#check @SerrePositivity.KST.SConstruction.identityUnionPushoutFamily_projection
#print axioms SerrePositivity.KST.SConstruction.identityUnionPushoutFamily_projection
#check @SerrePositivity.KST.SConstruction.exists_jointNormalizedPushoutSection
#print axioms SerrePositivity.KST.SConstruction.exists_jointNormalizedPushoutSection
#check @SerrePositivity.KST.SConstruction.jointNormalizedPushoutSection
#print axioms SerrePositivity.KST.SConstruction.jointNormalizedPushoutSection
#check @SerrePositivity.KST.SConstruction.jointNormalizedPushoutSection_projection
#print axioms SerrePositivity.KST.SConstruction.jointNormalizedPushoutSection_projection
#check @SerrePositivity.KST.SConstruction.jointNormalizedPushoutSection_union
#print axioms SerrePositivity.KST.SConstruction.jointNormalizedPushoutSection_union
#check @SerrePositivity.KST.SConstruction.jointNormalizedPushoutSection_identity
#print axioms SerrePositivity.KST.SConstruction.jointNormalizedPushoutSection_identity
#check @SerrePositivity.KST.SConstruction.jointNormalizedPushoutSection_comparison
#print axioms SerrePositivity.KST.SConstruction.jointNormalizedPushoutSection_comparison

#check @SerrePositivity.KST.SConstruction.flipFamily_evaluate
#print axioms SerrePositivity.KST.SConstruction.flipFamily_evaluate
#check @SerrePositivity.KST.SConstruction.normalizedPushoutSquareChoice
#print axioms SerrePositivity.KST.SConstruction.normalizedPushoutSquareChoice
#check @SerrePositivity.KST.SConstruction.normalizedPushoutSquareChoice_span
#print axioms SerrePositivity.KST.SConstruction.normalizedPushoutSquareChoice_span
#check @SerrePositivity.KST.SConstruction.normalizedPushoutSquareChoice_identity
#print axioms SerrePositivity.KST.SConstruction.normalizedPushoutSquareChoice_identity
#check @SerrePositivity.KST.SConstruction.chosenPushoutFamily
#print axioms SerrePositivity.KST.SConstruction.chosenPushoutFamily
#check @SerrePositivity.KST.SConstruction.chosenDiagramPushout
#print axioms SerrePositivity.KST.SConstruction.chosenDiagramPushout
#check @SerrePositivity.KST.SConstruction.chosenDiagramPushout_span
#print axioms SerrePositivity.KST.SConstruction.chosenDiagramPushout_span
#check @SerrePositivity.KST.SConstruction.chosenDiagramPushout_isPushout
#print axioms SerrePositivity.KST.SConstruction.chosenDiagramPushout_isPushout
#check @SerrePositivity.KST.SConstruction.chosenDiagramPushout_reindex
#print axioms SerrePositivity.KST.SConstruction.chosenDiagramPushout_reindex
#check @SerrePositivity.KST.SConstruction.chosenDiagramPushout_identity
#print axioms SerrePositivity.KST.SConstruction.chosenDiagramPushout_identity
#check @SerrePositivity.KST.SConstruction.selectedFunctorPushout
#print axioms SerrePositivity.KST.SConstruction.selectedFunctorPushout
#check @SerrePositivity.KST.SConstruction.selectedFunctorPushout_span
#print axioms SerrePositivity.KST.SConstruction.selectedFunctorPushout_span
#check @SerrePositivity.KST.SConstruction.selectedFunctorPushout_isPushout
#print axioms SerrePositivity.KST.SConstruction.selectedFunctorPushout_isPushout
#check @SerrePositivity.KST.SConstruction.selectedFunctorPushout_reindex
#print axioms SerrePositivity.KST.SConstruction.selectedFunctorPushout_reindex

#check @SerrePositivity.KST.SConstruction.exists_relative_zeroPrism
#print axioms SerrePositivity.KST.SConstruction.exists_relative_zeroPrism
#check @SerrePositivity.KST.SConstruction.zeroNaturalTransformation
#print axioms SerrePositivity.KST.SConstruction.zeroNaturalTransformation
#check @SerrePositivity.KST.SConstruction.zeroNaturalTransformation_zero
#print axioms SerrePositivity.KST.SConstruction.zeroNaturalTransformation_zero
#check @SerrePositivity.KST.SConstruction.zeroNaturalTransformation_one
#print axioms SerrePositivity.KST.SConstruction.zeroNaturalTransformation_one
#check @SerrePositivity.KST.SConstruction.zeroNaturalTransformation_fixed
#print axioms SerrePositivity.KST.SConstruction.zeroNaturalTransformation_fixed
#check @SerrePositivity.KST.SConstruction.zeroNaturalTransformation_constant
#print axioms SerrePositivity.KST.SConstruction.zeroNaturalTransformation_constant

#check @SerrePositivity.KST.SConstruction.isGapped_two_middle
#print axioms SerrePositivity.KST.SConstruction.isGapped_two_middle
#check @SerrePositivity.KST.SConstruction.sTwoCofiberRestriction
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberRestriction
#check @SerrePositivity.KST.SConstruction.sTwoCofiberRestriction_ι
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberRestriction_ι
#check @SerrePositivity.KST.SConstruction.sTwoCofiberRestriction_vertex_surjective
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberRestriction_vertex_surjective
#check @SerrePositivity.KST.SConstruction.sTwoCofiberRestriction_hasLiftingProperty_boundary
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberRestriction_hasLiftingProperty_boundary
#check @SerrePositivity.KST.SConstruction.sTwoCofiberRestriction_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberRestriction_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.cofiberDiagrams_quasicategory
#print axioms SerrePositivity.KST.SConstruction.cofiberDiagrams_quasicategory
#check @SerrePositivity.KST.SConstruction.cofiberDiagrams_isStable
#print axioms SerrePositivity.KST.SConstruction.cofiberDiagrams_isStable
#check @SerrePositivity.KST.SConstruction.sTwoCofiberRestriction_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberRestriction_preservesSConstructionData
#check @SerrePositivity.KST.SConstruction.cofiberStableModel
#print axioms SerrePositivity.KST.SConstruction.cofiberStableModel
#check @SerrePositivity.KST.SConstruction.sTwoCofiberComparison
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberComparison
#check @SerrePositivity.KST.SConstruction.sTwoCofiberSection
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberSection
#check @SerrePositivity.KST.SConstruction.sTwoCofiberSection_projection
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberSection_projection
#check @SerrePositivity.KST.SConstruction.sTwoCofiberSection_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberSection_preservesSConstructionData
#check @SerrePositivity.KST.SConstruction.sTwoCofiberInverse
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberInverse
#check @SerrePositivity.KST.SConstruction.sTwoCofiberSection_comparison
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberSection_comparison
#check @SerrePositivity.KST.SConstruction.sTwoCofiberEquivalence
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberEquivalence
#check @SerrePositivity.KST.SConstruction.sTwoCofiberComparison_realization_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberComparison_realization_localized_isIso

#check @SerrePositivity.KST.SConstruction.intervalMinOrder
#print axioms SerrePositivity.KST.SConstruction.intervalMinOrder
#check @SerrePositivity.KST.SConstruction.intervalMin
#print axioms SerrePositivity.KST.SConstruction.intervalMin
#check @SerrePositivity.KST.SConstruction.intervalMin_app_zero
#print axioms SerrePositivity.KST.SConstruction.intervalMin_app_zero
#check @SerrePositivity.KST.SConstruction.intervalMin_app_one
#print axioms SerrePositivity.KST.SConstruction.intervalMin_app_one
#check @SerrePositivity.KST.SConstruction.variableTimeShape
#print axioms SerrePositivity.KST.SConstruction.variableTimeShape
#check @SerrePositivity.KST.SConstruction.variableTimeShape_zero
#print axioms SerrePositivity.KST.SConstruction.variableTimeShape_zero
#check @SerrePositivity.KST.SConstruction.variableTimeShape_one
#print axioms SerrePositivity.KST.SConstruction.variableTimeShape_one
#check @SerrePositivity.KST.SConstruction.variableTimeImage
#print axioms SerrePositivity.KST.SConstruction.variableTimeImage
#check @SerrePositivity.KST.SConstruction.variableTimeImage_pre
#print axioms SerrePositivity.KST.SConstruction.variableTimeImage_pre
#check @SerrePositivity.KST.SConstruction.variableTimeImage_zero
#print axioms SerrePositivity.KST.SConstruction.variableTimeImage_zero
#check @SerrePositivity.KST.SConstruction.variableTimeImage_one
#print axioms SerrePositivity.KST.SConstruction.variableTimeImage_one
#check @SerrePositivity.KST.SConstruction.variableTimeHomotopy
#print axioms SerrePositivity.KST.SConstruction.variableTimeHomotopy
#check @SerrePositivity.KST.SConstruction.variableTimeHomotopy_isInvertible
#print axioms SerrePositivity.KST.SConstruction.variableTimeHomotopy_isInvertible
#check @SerrePositivity.KST.SConstruction.variableTimeImageIso
#print axioms SerrePositivity.KST.SConstruction.variableTimeImageIso
#check @SerrePositivity.KST.SConstruction.IsGapped.variableTimeImage
#print axioms SerrePositivity.KST.SConstruction.IsGapped.variableTimeImage
#check @SerrePositivity.KST.SConstruction.gappedObjectVertex
#print axioms SerrePositivity.KST.SConstruction.gappedObjectVertex
#check @SerrePositivity.KST.SConstruction.gappedDiagram_gappedObjectVertex
#print axioms SerrePositivity.KST.SConstruction.gappedDiagram_gappedObjectVertex
#check @SerrePositivity.KST.SConstruction.gappedDiagram_injective
#print axioms SerrePositivity.KST.SConstruction.gappedDiagram_injective
#check @SerrePositivity.KST.SConstruction.gappedDiagram_sMap
#print axioms SerrePositivity.KST.SConstruction.gappedDiagram_sMap
#check @SerrePositivity.KST.SConstruction.gappedDiagram_objectS_map
#print axioms SerrePositivity.KST.SConstruction.gappedDiagram_objectS_map
#check @SerrePositivity.KST.SConstruction.gappedDiagram_sPostcompCofiber
#print axioms SerrePositivity.KST.SConstruction.gappedDiagram_sPostcompCofiber
#check @SerrePositivity.KST.SConstruction.gappedDiagram_objectSFunctor_map
#print axioms SerrePositivity.KST.SConstruction.gappedDiagram_objectSFunctor_map
#check @SerrePositivity.KST.SConstruction.arFirstEndpointOrder
#print axioms SerrePositivity.KST.SConstruction.arFirstEndpointOrder
#check @SerrePositivity.KST.SConstruction.arFirstEndpoint
#print axioms SerrePositivity.KST.SConstruction.arFirstEndpoint
#check @SerrePositivity.KST.SConstruction.arTimeCoordinate
#print axioms SerrePositivity.KST.SConstruction.arTimeCoordinate
#check @SerrePositivity.KST.SConstruction.arTimeCoordinate_naturality
#print axioms SerrePositivity.KST.SConstruction.arTimeCoordinate_naturality
#check @SerrePositivity.KST.SConstruction.arTimeCoordinate_constant
#print axioms SerrePositivity.KST.SConstruction.arTimeCoordinate_constant
#check @SerrePositivity.KST.SConstruction.objectSHomotopyVertex
#print axioms SerrePositivity.KST.SConstruction.objectSHomotopyVertex
#check @SerrePositivity.KST.SConstruction.objectSHomotopyVertex_diagram
#print axioms SerrePositivity.KST.SConstruction.objectSHomotopyVertex_diagram
#check @SerrePositivity.KST.SConstruction.objectSHomotopyMap
#print axioms SerrePositivity.KST.SConstruction.objectSHomotopyMap
#check @SerrePositivity.KST.SConstruction.objectSHomotopy
#print axioms SerrePositivity.KST.SConstruction.objectSHomotopy
#check @SerrePositivity.KST.SConstruction.objectSHomotopyOfFunctorIso
#print axioms SerrePositivity.KST.SConstruction.objectSHomotopyOfFunctorIso
#check @SerrePositivity.KST.SConstruction.preservesSConstructionData_section_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.preservesSConstructionData_section_of_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.objectS_map_isSimplicialHomotopyEquivalence_of_inverse
#print axioms SerrePositivity.KST.SConstruction.objectS_map_isSimplicialHomotopyEquivalence_of_inverse
#check @SerrePositivity.KST.SConstruction.objectS_map_isSimplicialHomotopyEquivalence_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.objectS_map_isSimplicialHomotopyEquivalence_of_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.objectS_map_localized_isIso_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.objectS_map_localized_isIso_of_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.sTwoCofiberComparison_objectS_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberComparison_objectS_localized_isIso

#check @SerrePositivity.KST.SConstruction.IsEquivalenceDiagramVertex
#print axioms SerrePositivity.KST.SConstruction.IsEquivalenceDiagramVertex
#check @SerrePositivity.KST.SConstruction.equivalenceDiagrams
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagrams
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramι
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramι
#check @SerrePositivity.KST.SConstruction.equivalenceDiagrams_quasicategory
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagrams_quasicategory
#check @SerrePositivity.KST.SConstruction.isEquivalenceDiagramVertex_functorVertex
#print axioms SerrePositivity.KST.SConstruction.isEquivalenceDiagramVertex_functorVertex
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramReindex
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramReindex
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramReindex_ι
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramReindex_ι
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramEvaluation
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramEvaluation
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramConstant
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramConstant
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramConstant_ι
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramConstant_ι
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramConstant_evaluation
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramConstant_evaluation
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramReindex_id
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramReindex_id
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramReindex_comp
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramReindex_comp
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramReindex_evaluation
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramReindex_evaluation
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramConstant_reindex
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramConstant_reindex
#check @SerrePositivity.KST.SConstruction.simplicialEquivalenceDiagrams
#print axioms SerrePositivity.KST.SConstruction.simplicialEquivalenceDiagrams
#check @SerrePositivity.KST.SConstruction.constantEquivalenceDiagramNat
#print axioms SerrePositivity.KST.SConstruction.constantEquivalenceDiagramNat
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramVertexOfCoreMap
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramVertexOfCoreMap
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramCoreMap
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramCoreMap
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramVerticesEquiv
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramVerticesEquiv
#check @SerrePositivity.KST.SConstruction.pointFunctorEvaluationIso
#print axioms SerrePositivity.KST.SConstruction.pointFunctorEvaluationIso
#check @SerrePositivity.KST.SConstruction.evaluateFunctorAt_factor
#print axioms SerrePositivity.KST.SConstruction.evaluateFunctorAt_factor
#check @SerrePositivity.KST.SConstruction.evaluateFunctorAt_innerFibration
#print axioms SerrePositivity.KST.SConstruction.evaluateFunctorAt_innerFibration
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramEvaluation_innerFibration
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramEvaluation_innerFibration
#check @SerrePositivity.KST.SConstruction.zeroEquivalenceDiagramEvaluationIso
#print axioms SerrePositivity.KST.SConstruction.zeroEquivalenceDiagramEvaluationIso
#check @SerrePositivity.KST.SConstruction.zeroEquivalenceDiagramEvaluation_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroEquivalenceDiagramEvaluation_isIso
#check @SerrePositivity.KST.SConstruction.simplexInitialOrder
#print axioms SerrePositivity.KST.SConstruction.simplexInitialOrder
#check @SerrePositivity.KST.SConstruction.simplexInitialContraction
#print axioms SerrePositivity.KST.SConstruction.simplexInitialContraction
#check @SerrePositivity.KST.SConstruction.simplexInitialContraction_zero
#print axioms SerrePositivity.KST.SConstruction.simplexInitialContraction_zero
#check @SerrePositivity.KST.SConstruction.simplexInitialContraction_one
#print axioms SerrePositivity.KST.SConstruction.simplexInitialContraction_one
#check @SerrePositivity.KST.SConstruction.simplexInitialContraction_firstVertex
#print axioms SerrePositivity.KST.SConstruction.simplexInitialContraction_firstVertex
#check @SerrePositivity.KST.SConstruction.restrictedPrecompositionIso
#print axioms SerrePositivity.KST.SConstruction.restrictedPrecompositionIso
#check @SerrePositivity.KST.SConstruction.pre_constant_evaluation
#print axioms SerrePositivity.KST.SConstruction.pre_constant_evaluation
#check @SerrePositivity.KST.SConstruction.simplexInitialHomotopy
#print axioms SerrePositivity.KST.SConstruction.simplexInitialHomotopy
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramEvaluation_comparison
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramEvaluation_comparison
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramEvaluationEquivalence
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramEvaluationEquivalence
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramEvaluation_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramEvaluation_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.equivalenceDiagrams_isStable
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagrams_isStable
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramStableModel
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramStableModel
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramStableEvaluation
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramStableEvaluation
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramStableConstant
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramStableConstant
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramStableConstant_evaluation
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramStableConstant_evaluation
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramStableEvaluation_objectS_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramStableEvaluation_objectS_localized_isIso
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramStableConstant_objectS_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramStableConstant_objectS_localized_isIso
#check @SerrePositivity.KST.SConstruction.PreservesSConstructionData.of_functorIso
#print axioms SerrePositivity.KST.SConstruction.PreservesSConstructionData.of_functorIso
#check @SerrePositivity.KST.SConstruction.evaluateFunctorAt_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.evaluateFunctorAt_preservesSConstructionData
#check @SerrePositivity.KST.SConstruction.constantFunctor_evaluation
#print axioms SerrePositivity.KST.SConstruction.constantFunctor_evaluation
#check @SerrePositivity.KST.SConstruction.constantFunctor_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.constantFunctor_preservesSConstructionData
#check @SerrePositivity.KST.SConstruction.equivalenceDiagramι_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.equivalenceDiagramι_preservesSConstructionData
#check @SerrePositivity.KST.SConstruction.isGapped_functor_iff_pointwise
#print axioms SerrePositivity.KST.SConstruction.isGapped_functor_iff_pointwise
#check @SerrePositivity.KST.SConstruction.isGapped_equivalenceDiagramι_iff
#print axioms SerrePositivity.KST.SConstruction.isGapped_equivalenceDiagramι_iff
#check @SerrePositivity.KST.SConstruction.diagramSpace_quasicategory
#print axioms SerrePositivity.KST.SConstruction.diagramSpace_quasicategory
#check @SerrePositivity.KST.SConstruction.gappedFamilyLift
#print axioms SerrePositivity.KST.SConstruction.gappedFamilyLift
#check @SerrePositivity.KST.SConstruction.gappedFamilyLift_ι
#print axioms SerrePositivity.KST.SConstruction.gappedFamilyLift_ι
#check @SerrePositivity.KST.SConstruction.coreGappedFamilyLift
#print axioms SerrePositivity.KST.SConstruction.coreGappedFamilyLift
#check @SerrePositivity.KST.SConstruction.coreGappedFamilyLift_ι
#print axioms SerrePositivity.KST.SConstruction.coreGappedFamilyLift_ι
#check @SerrePositivity.KST.SConstruction.flipFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.flipFamily_vertex
#check @SerrePositivity.KST.SConstruction.isInvertibleFunctorEdge_iff_pointwise
#print axioms SerrePositivity.KST.SConstruction.isInvertibleFunctorEdge_iff_pointwise
#check @SerrePositivity.KST.SConstruction.flipEquivalenceDiagram_edge
#print axioms SerrePositivity.KST.SConstruction.flipEquivalenceDiagram_edge
#check @SerrePositivity.KST.SConstruction.flipGappedEquivalenceDiagram_vertex
#print axioms SerrePositivity.KST.SConstruction.flipGappedEquivalenceDiagram_vertex
#check @SerrePositivity.KST.SConstruction.gappedEquivalenceDiagramCoreMap
#print axioms SerrePositivity.KST.SConstruction.gappedEquivalenceDiagramCoreMap
#check @SerrePositivity.KST.SConstruction.gappedEquivalenceDiagramCoreMap_ι
#print axioms SerrePositivity.KST.SConstruction.gappedEquivalenceDiagramCoreMap_ι
#check @SerrePositivity.KST.SConstruction.flipCoreGappedFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.flipCoreGappedFamily_vertex
#check @SerrePositivity.KST.SConstruction.coreGappedEquivalenceDiagram
#print axioms SerrePositivity.KST.SConstruction.coreGappedEquivalenceDiagram
#check @SerrePositivity.KST.SConstruction.coreGappedEquivalenceDiagram_ι
#print axioms SerrePositivity.KST.SConstruction.coreGappedEquivalenceDiagram_ι
#check @SerrePositivity.KST.SConstruction.coreGappedEquivalenceDiagram_isGapped
#print axioms SerrePositivity.KST.SConstruction.coreGappedEquivalenceDiagram_isGapped
#check @SerrePositivity.KST.SConstruction.coreGappedEquivalenceDiagramVertex
#print axioms SerrePositivity.KST.SConstruction.coreGappedEquivalenceDiagramVertex
#check @SerrePositivity.KST.SConstruction.gappedEquivalenceDiagramVerticesEquiv
#print axioms SerrePositivity.KST.SConstruction.gappedEquivalenceDiagramVerticesEquiv
#check @SerrePositivity.KST.SConstruction.gappedEquivalenceDiagramCoreMap_sMap
#print axioms SerrePositivity.KST.SConstruction.gappedEquivalenceDiagramCoreMap_sMap
#check @SerrePositivity.KST.SConstruction.objectCoreRowIso
#print axioms SerrePositivity.KST.SConstruction.objectCoreRowIso
#check @SerrePositivity.KST.SConstruction.objectRowInclusion
#print axioms SerrePositivity.KST.SConstruction.objectRowInclusion
#check @SerrePositivity.KST.SConstruction.objectRowsInclusion
#print axioms SerrePositivity.KST.SConstruction.objectRowsInclusion
#check @SerrePositivity.KST.SConstruction.diagonalFlipIso
#print axioms SerrePositivity.KST.SConstruction.diagonalFlipIso
#check @SerrePositivity.KST.SConstruction.diagonalConstIso
#print axioms SerrePositivity.KST.SConstruction.diagonalConstIso
#check @SerrePositivity.KST.SConstruction.objectRowsInclusion_diagonal
#print axioms SerrePositivity.KST.SConstruction.objectRowsInclusion_diagonal
#check @SerrePositivity.KST.SConstruction.flipConstantFamily
#print axioms SerrePositivity.KST.SConstruction.flipConstantFamily
#check @SerrePositivity.KST.SConstruction.gappedEquivalenceDiagramCoreMap_constant
#print axioms SerrePositivity.KST.SConstruction.gappedEquivalenceDiagramCoreMap_constant
#check @SerrePositivity.KST.SConstruction.objectCoreRowIso_constant
#print axioms SerrePositivity.KST.SConstruction.objectCoreRowIso_constant
#check @SerrePositivity.KST.SConstruction.objectRowInclusion_coreS_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.objectRowInclusion_coreS_localized_isIso
#check @SerrePositivity.KST.SConstruction.diagonalObjectInclusion_coreS_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.diagonalObjectInclusion_coreS_localized_isIso
#check @SerrePositivity.KST.SConstruction.objectToCoreSRealization_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.objectToCoreSRealization_localized_isIso
#check @SerrePositivity.KST.SConstruction.zeroCofiberSquare
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberSquare
#check @SerrePositivity.KST.SConstruction.zeroCofiberSquare_evaluation
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberSquare_evaluation
#check @SerrePositivity.KST.SConstruction.zeroCofiberSquare_vertex_isPushout
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberSquare_vertex_isPushout
#check @SerrePositivity.KST.SConstruction.zeroCofiberFunctor
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberFunctor
#check @SerrePositivity.KST.SConstruction.zeroCofiberFunctor_ι
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberFunctor_ι
#check @SerrePositivity.KST.SConstruction.zeroCofiberFunctor_input_evaluation
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberFunctor_input_evaluation
#check @SerrePositivity.KST.SConstruction.zeroCofiberFunctor_quotient
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberFunctor_quotient
#check @SerrePositivity.KST.SConstruction.constantZero_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.constantZero_preservesSConstructionData
#check @SerrePositivity.KST.SConstruction.preservesSConstructionData_functor_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.preservesSConstructionData_functor_of_pointwise
#check @SerrePositivity.KST.SConstruction.preservesSConstructionData_of_comp_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.preservesSConstructionData_of_comp_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.zeroCofiberFunctor_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberFunctor_preservesSConstructionData
#check @SerrePositivity.KST.SConstruction.pre_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.pre_preservesSConstructionData
#check @SerrePositivity.KST.SConstruction.cofiberInclusion_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.cofiberInclusion_preservesSConstructionData
#check @SerrePositivity.KST.SConstruction.cofiberEvaluation_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.cofiberEvaluation_preservesSConstructionData
#check @SerrePositivity.KST.SConstruction.cofiberStableEvaluation
#print axioms SerrePositivity.KST.SConstruction.cofiberStableEvaluation
#check @SerrePositivity.KST.SConstruction.cofiberStableSubobject
#print axioms SerrePositivity.KST.SConstruction.cofiberStableSubobject
#check @SerrePositivity.KST.SConstruction.cofiberStableMiddle
#print axioms SerrePositivity.KST.SConstruction.cofiberStableMiddle
#check @SerrePositivity.KST.SConstruction.cofiberStableQuotient
#print axioms SerrePositivity.KST.SConstruction.cofiberStableQuotient
#check @SerrePositivity.KST.SConstruction.zeroCofiberStableFunctor
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberStableFunctor
#check @SerrePositivity.KST.SConstruction.zeroCofiberStableFunctor_subobject
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberStableFunctor_subobject
#check @SerrePositivity.KST.SConstruction.zeroCofiberStableFunctor_quotient
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberStableFunctor_quotient
#check @SerrePositivity.KST.SConstruction.simplexLeftFiber
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiber
#check @SerrePositivity.KST.SConstruction.simplexLeftFiberProjection
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiberProjection
#check @SerrePositivity.KST.SConstruction.simplexLeftFiberParameter
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiberParameter
#check @SerrePositivity.KST.SConstruction.simplexLeftFiber_condition
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiber_condition
#check @SerrePositivity.KST.SConstruction.simplexLeftFiberLift
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiberLift
#check @SerrePositivity.KST.SConstruction.simplexLeftFiberLift_projection
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiberLift_projection
#check @SerrePositivity.KST.SConstruction.simplexLeftFiberLift_parameter
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiberLift_parameter
#check @SerrePositivity.KST.SConstruction.simplexLeftFiber_hom_ext
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiber_hom_ext
#check @SerrePositivity.KST.SConstruction.simplexLeftFiberMap
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiberMap
#check @SerrePositivity.KST.SConstruction.simplexLeftFiberMap_projection
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiberMap_projection
#check @SerrePositivity.KST.SConstruction.simplexLeftFiberMap_parameter
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiberMap_parameter
#check @SerrePositivity.KST.SConstruction.simplexLeftFiberSimplexEquiv
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiberSimplexEquiv
#check @SerrePositivity.KST.SConstruction.simplexLeftFiberMap_postcomp
#print axioms SerrePositivity.KST.SConstruction.simplexLeftFiberMap_postcomp
#check @SerrePositivity.KST.SConstruction.cofiberSubobjectLeftFiber
#print axioms SerrePositivity.KST.SConstruction.cofiberSubobjectLeftFiber
#check @SerrePositivity.KST.SConstruction.cofiberLeftFiberQuotient
#print axioms SerrePositivity.KST.SConstruction.cofiberLeftFiberQuotient
#check @SerrePositivity.KST.SConstruction.arNerveMap_const
#print axioms SerrePositivity.KST.SConstruction.arNerveMap_const
#check @SerrePositivity.KST.SConstruction.gappedDiagram_objectS_const
#print axioms SerrePositivity.KST.SConstruction.gappedDiagram_objectS_const
#check @SerrePositivity.KST.SConstruction.objectSLastDiagonalZeroVertex
#print axioms SerrePositivity.KST.SConstruction.objectSLastDiagonalZeroVertex
#check @SerrePositivity.KST.SConstruction.stableConstantZero
#print axioms SerrePositivity.KST.SConstruction.stableConstantZero
#check @SerrePositivity.KST.SConstruction.objectS_lastVertex_constantZero
#print axioms SerrePositivity.KST.SConstruction.objectS_lastVertex_constantZero
#check @SerrePositivity.KST.SConstruction.zeroCofiberStableFunctor_subobject_true
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberStableFunctor_subobject_true
#check @SerrePositivity.KST.SConstruction.mcCarthyFiberSection
#print axioms SerrePositivity.KST.SConstruction.mcCarthyFiberSection
#check @SerrePositivity.KST.SConstruction.mcCarthyFiberSection_projection
#print axioms SerrePositivity.KST.SConstruction.mcCarthyFiberSection_projection
#check @SerrePositivity.KST.SConstruction.mcCarthyFiberSection_parameter
#print axioms SerrePositivity.KST.SConstruction.mcCarthyFiberSection_parameter
#check @SerrePositivity.KST.SConstruction.mcCarthyFiberSection_quotient
#print axioms SerrePositivity.KST.SConstruction.mcCarthyFiberSection_quotient
#check @SerrePositivity.KST.SConstruction.orderPrismOrder
#print axioms SerrePositivity.KST.SConstruction.orderPrismOrder
#check @SerrePositivity.KST.SConstruction.orderPrism
#print axioms SerrePositivity.KST.SConstruction.orderPrism
#check @SerrePositivity.KST.SConstruction.orderPrism_zero
#print axioms SerrePositivity.KST.SConstruction.orderPrism_zero
#check @SerrePositivity.KST.SConstruction.orderPrism_one
#print axioms SerrePositivity.KST.SConstruction.orderPrism_one
#check @SerrePositivity.KST.SConstruction.orderPrism_pre
#print axioms SerrePositivity.KST.SConstruction.orderPrism_pre
#check @SerrePositivity.KST.SConstruction.orderPrism_post
#print axioms SerrePositivity.KST.SConstruction.orderPrism_post
#check @SerrePositivity.KST.SConstruction.orderPrism_refl
#print axioms SerrePositivity.KST.SConstruction.orderPrism_refl
#check @SerrePositivity.KST.SConstruction.orderPrism_of_eq
#print axioms SerrePositivity.KST.SConstruction.orderPrism_of_eq
#check @SerrePositivity.KST.SConstruction.mcCarthyMovedOrder
#print axioms SerrePositivity.KST.SConstruction.mcCarthyMovedOrder
#check @SerrePositivity.KST.SConstruction.mcCarthyMovedOrder_le
#print axioms SerrePositivity.KST.SConstruction.mcCarthyMovedOrder_le
#check @SerrePositivity.KST.SConstruction.mcCarthyMovedOrder_comp
#print axioms SerrePositivity.KST.SConstruction.mcCarthyMovedOrder_comp
#check @SerrePositivity.KST.SConstruction.mcCarthyMovedOrder_zero
#print axioms SerrePositivity.KST.SConstruction.mcCarthyMovedOrder_zero
#check @SerrePositivity.KST.SConstruction.mcCarthyMovedOrder_one
#print axioms SerrePositivity.KST.SConstruction.mcCarthyMovedOrder_one
#check @SerrePositivity.KST.SConstruction.mcCarthyMovedOrder_simplex
#print axioms SerrePositivity.KST.SConstruction.mcCarthyMovedOrder_simplex
#check @SerrePositivity.KST.SConstruction.mcCarthyArMotion
#print axioms SerrePositivity.KST.SConstruction.mcCarthyArMotion
#check @SerrePositivity.KST.SConstruction.mcCarthyArMotion_zero
#print axioms SerrePositivity.KST.SConstruction.mcCarthyArMotion_zero
#check @SerrePositivity.KST.SConstruction.mcCarthyArMotion_one
#print axioms SerrePositivity.KST.SConstruction.mcCarthyArMotion_one
#check @SerrePositivity.KST.SConstruction.mcCarthyArMotion_pre
#print axioms SerrePositivity.KST.SConstruction.mcCarthyArMotion_pre
#check @SerrePositivity.KST.SConstruction.mcCarthyArMotion_timeZero
#print axioms SerrePositivity.KST.SConstruction.mcCarthyArMotion_timeZero
#check @SerrePositivity.KST.SConstruction.mcCarthyLambda
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambda
#check @SerrePositivity.KST.SConstruction.mcCarthyMu
#print axioms SerrePositivity.KST.SConstruction.mcCarthyMu
#check @SerrePositivity.KST.SConstruction.mcCarthyLambdaMu
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambdaMu
#check @SerrePositivity.KST.SConstruction.mcCarthyLambdaMu_zero
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambdaMu_zero
#check @SerrePositivity.KST.SConstruction.mcCarthyLambdaMu_one
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambdaMu_one
#check @SerrePositivity.KST.SConstruction.mcCarthyLambdaMu_pre
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambdaMu_pre
#check @SerrePositivity.KST.SConstruction.mcCarthyLambda_isGapped
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambda_isGapped
#check @SerrePositivity.KST.SConstruction.mcCarthyMu_isGapped
#print axioms SerrePositivity.KST.SConstruction.mcCarthyMu_isGapped
#check @SerrePositivity.KST.SConstruction.mcCarthyLambdaMu_timeZero
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambdaMu_timeZero
#check @SerrePositivity.KST.SConstruction.exists_lift_prism_of_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.exists_lift_prism_of_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.liftPrismOfTrivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.liftPrismOfTrivialKanFibration
#check @SerrePositivity.KST.SConstruction.liftPrismOfTrivialKanFibration_zero
#print axioms SerrePositivity.KST.SConstruction.liftPrismOfTrivialKanFibration_zero
#check @SerrePositivity.KST.SConstruction.liftPrismOfTrivialKanFibration_one
#print axioms SerrePositivity.KST.SConstruction.liftPrismOfTrivialKanFibration_one
#check @SerrePositivity.KST.SConstruction.liftPrismOfTrivialKanFibration_projection
#print axioms SerrePositivity.KST.SConstruction.liftPrismOfTrivialKanFibration_projection
#check @SerrePositivity.KST.SConstruction.arrowSourcePrism
#print axioms SerrePositivity.KST.SConstruction.arrowSourcePrism
#check @SerrePositivity.KST.SConstruction.arrowSourcePrism_zero
#print axioms SerrePositivity.KST.SConstruction.arrowSourcePrism_zero
#check @SerrePositivity.KST.SConstruction.arrowSourcePrism_one
#print axioms SerrePositivity.KST.SConstruction.arrowSourcePrism_one
#check @SerrePositivity.KST.SConstruction.arrowSourcePrism_source
#print axioms SerrePositivity.KST.SConstruction.arrowSourcePrism_source
#check @SerrePositivity.KST.SConstruction.zeroCofiberFunctor_identityProjection
#print axioms SerrePositivity.KST.SConstruction.zeroCofiberFunctor_identityProjection
#check @SerrePositivity.KST.SConstruction.cofiberLambdaNu
#print axioms SerrePositivity.KST.SConstruction.cofiberLambdaNu
#check @SerrePositivity.KST.SConstruction.cofiberLambdaNu_zero
#print axioms SerrePositivity.KST.SConstruction.cofiberLambdaNu_zero
#check @SerrePositivity.KST.SConstruction.cofiberLambdaNu_one
#print axioms SerrePositivity.KST.SConstruction.cofiberLambdaNu_one
#check @SerrePositivity.KST.SConstruction.cofiberLambdaNu_projection
#print axioms SerrePositivity.KST.SConstruction.cofiberLambdaNu_projection
#check @SerrePositivity.KST.SConstruction.cofiberLambdaNu_source
#print axioms SerrePositivity.KST.SConstruction.cofiberLambdaNu_source
#check @SerrePositivity.KST.SConstruction.mcCarthyLambdaNu
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambdaNu
#check @SerrePositivity.KST.SConstruction.mcCarthyLambdaNu_pre
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambdaNu_pre
#check @SerrePositivity.KST.SConstruction.mcCarthyLambdaNu_zero
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambdaNu_zero
#check @SerrePositivity.KST.SConstruction.mcCarthyLambdaNu_one
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambdaNu_one
#check @SerrePositivity.KST.SConstruction.mcCarthyLambdaNu_source
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambdaNu_source
#check @SerrePositivity.KST.SConstruction.spanPrism_source
#print axioms SerrePositivity.KST.SConstruction.spanPrism_source
#check @SerrePositivity.KST.SConstruction.spanPrisms_isPushout
#print axioms SerrePositivity.KST.SConstruction.spanPrisms_isPushout
#check @SerrePositivity.KST.SConstruction.spanPrisms
#print axioms SerrePositivity.KST.SConstruction.spanPrisms
#check @SerrePositivity.KST.SConstruction.spanPrisms_left
#print axioms SerrePositivity.KST.SConstruction.spanPrisms_left
#check @SerrePositivity.KST.SConstruction.spanPrisms_right
#print axioms SerrePositivity.KST.SConstruction.spanPrisms_right
#check @SerrePositivity.KST.SConstruction.spanPrisms_hom_ext
#print axioms SerrePositivity.KST.SConstruction.spanPrisms_hom_ext
#check @SerrePositivity.KST.SConstruction.spanPrisms_post
#print axioms SerrePositivity.KST.SConstruction.spanPrisms_post
#check @SerrePositivity.KST.SConstruction.spanPrisms_pre
#print axioms SerrePositivity.KST.SConstruction.spanPrisms_pre
#check @SerrePositivity.KST.SConstruction.spanPrisms_constant_left
#print axioms SerrePositivity.KST.SConstruction.spanPrisms_constant_left
#check @SerrePositivity.KST.SConstruction.mcCarthySpan
#print axioms SerrePositivity.KST.SConstruction.mcCarthySpan
#check @SerrePositivity.KST.SConstruction.mcCarthySpan_upper
#print axioms SerrePositivity.KST.SConstruction.mcCarthySpan_upper
#check @SerrePositivity.KST.SConstruction.mcCarthySpan_left
#print axioms SerrePositivity.KST.SConstruction.mcCarthySpan_left
#check @SerrePositivity.KST.SConstruction.mcCarthySpan_pre
#print axioms SerrePositivity.KST.SConstruction.mcCarthySpan_pre
#check @SerrePositivity.KST.SConstruction.mcCarthyLambdaMu_source
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambdaMu_source
#check @SerrePositivity.KST.SConstruction.mcCarthySpan_timeZero
#print axioms SerrePositivity.KST.SConstruction.mcCarthySpan_timeZero
#check @SerrePositivity.KST.SConstruction.exchangeFirstTwo
#print axioms SerrePositivity.KST.SConstruction.exchangeFirstTwo
#check @SerrePositivity.KST.SConstruction.exchangeFirstTwo_naturality
#print axioms SerrePositivity.KST.SConstruction.exchangeFirstTwo_naturality
#check @SerrePositivity.KST.SConstruction.exchangeDiagramFamily
#print axioms SerrePositivity.KST.SConstruction.exchangeDiagramFamily
#check @SerrePositivity.KST.SConstruction.exchangeDiagramFamily_pre
#print axioms SerrePositivity.KST.SConstruction.exchangeDiagramFamily_pre
#check @SerrePositivity.KST.SConstruction.exchangeFirstTwo_naturality_left
#print axioms SerrePositivity.KST.SConstruction.exchangeFirstTwo_naturality_left
#check @SerrePositivity.KST.SConstruction.exchangeDiagramFamily_pre_left
#print axioms SerrePositivity.KST.SConstruction.exchangeDiagramFamily_pre_left
#check @SerrePositivity.KST.SConstruction.exchangeDiagramFamily_evaluation_interval
#print axioms SerrePositivity.KST.SConstruction.exchangeDiagramFamily_evaluation_interval
#check @SerrePositivity.KST.SConstruction.pointwisePushoutApex
#print axioms SerrePositivity.KST.SConstruction.pointwisePushoutApex
#check @SerrePositivity.KST.SConstruction.pointwisePushoutApex_pre
#print axioms SerrePositivity.KST.SConstruction.pointwisePushoutApex_pre
#check @SerrePositivity.KST.SConstruction.pointwiseDiagramPushoutApex
#print axioms SerrePositivity.KST.SConstruction.pointwiseDiagramPushoutApex
#check @SerrePositivity.KST.SConstruction.pointwiseDiagramPushoutApex_pre
#print axioms SerrePositivity.KST.SConstruction.pointwiseDiagramPushoutApex_pre
#check @SerrePositivity.KST.SConstruction.pointwisePushoutApex_identity
#print axioms SerrePositivity.KST.SConstruction.pointwisePushoutApex_identity
#check @SerrePositivity.KST.SConstruction.pointwiseDiagramPushoutApex_identity
#print axioms SerrePositivity.KST.SConstruction.pointwiseDiagramPushoutApex_identity
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoRaw
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoRaw
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoRaw_pre
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoRaw_pre
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoRaw_timeZero
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoRaw_timeZero

#check @SerrePositivity.KST.SConstruction.pointwiseDiagramPushout
#print axioms SerrePositivity.KST.SConstruction.pointwiseDiagramPushout
#check @SerrePositivity.KST.SConstruction.ihomCurry_evaluate_pair
#print axioms SerrePositivity.KST.SConstruction.ihomCurry_evaluate_pair
#check @SerrePositivity.KST.SConstruction.pointwiseDiagramPushout_evaluate
#print axioms SerrePositivity.KST.SConstruction.pointwiseDiagramPushout_evaluate
#check @SerrePositivity.KST.SConstruction.pointwiseDiagramPushout_isPushout
#print axioms SerrePositivity.KST.SConstruction.pointwiseDiagramPushout_isPushout
#check @SerrePositivity.KST.SConstruction.pointwiseDiagramPushout_span
#print axioms SerrePositivity.KST.SConstruction.pointwiseDiagramPushout_span
#check @SerrePositivity.KST.SConstruction.pointwiseDiagramPushout_apex
#print axioms SerrePositivity.KST.SConstruction.pointwiseDiagramPushout_apex
#check @SerrePositivity.KST.SConstruction.chosenDiagramPushout_apex
#print axioms SerrePositivity.KST.SConstruction.chosenDiagramPushout_apex
#check @SerrePositivity.KST.SConstruction.pointwiseDiagramPushoutApex_postcompIso
#print axioms SerrePositivity.KST.SConstruction.pointwiseDiagramPushoutApex_postcompIso
#check @SerrePositivity.KST.SConstruction.IsCofiberDiagramVertex.of_vertexIso
#print axioms SerrePositivity.KST.SConstruction.IsCofiberDiagramVertex.of_vertexIso
#check @SerrePositivity.KST.SConstruction.pointwiseCofiberPushout_vertex
#print axioms SerrePositivity.KST.SConstruction.pointwiseCofiberPushout_vertex
#check @SerrePositivity.KST.SConstruction.pointwiseCofiberPushout
#print axioms SerrePositivity.KST.SConstruction.pointwiseCofiberPushout
#check @SerrePositivity.KST.SConstruction.pointwiseCofiberPushout_ι
#print axioms SerrePositivity.KST.SConstruction.pointwiseCofiberPushout_ι
#check @SerrePositivity.KST.SConstruction.pointwisePushoutApex_isGapped
#print axioms SerrePositivity.KST.SConstruction.pointwisePushoutApex_isGapped
#check @SerrePositivity.KST.SConstruction.pointwiseCofiberPushout_iso
#print axioms SerrePositivity.KST.SConstruction.pointwiseCofiberPushout_iso
#check @SerrePositivity.KST.SConstruction.pointwiseCofiberPushout_isGapped
#print axioms SerrePositivity.KST.SConstruction.pointwiseCofiberPushout_isGapped
#check @SerrePositivity.KST.SConstruction.transposeFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.transposeFamily_vertex
#check @SerrePositivity.KST.SConstruction.transposeFamily_interval_vertex
#print axioms SerrePositivity.KST.SConstruction.transposeFamily_interval_vertex
#check @SerrePositivity.KST.SConstruction.mcCarthySpan_isGapped_vertex
#print axioms SerrePositivity.KST.SConstruction.mcCarthySpan_isGapped_vertex
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoRaw_isCofiber
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoRaw_isCofiber
#check @SerrePositivity.KST.SConstruction.mcCarthyRho
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRho
#check @SerrePositivity.KST.SConstruction.mcCarthyRho_ι
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRho_ι
#check @SerrePositivity.KST.SConstruction.mcCarthyRho_timeZero
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRho_timeZero
#check @SerrePositivity.KST.SConstruction.mcCarthyRho_pre
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRho_pre
#check @SerrePositivity.KST.SConstruction.mcCarthyRho_isGapped
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRho_isGapped
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoRaw_isGapped
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoRaw_isGapped

#check @SerrePositivity.KST.SConstruction.exchangeDiagramFamily_evaluate
#print axioms SerrePositivity.KST.SConstruction.exchangeDiagramFamily_evaluate
#check @SerrePositivity.KST.SConstruction.pointwiseDiagramPushoutApex_evaluate
#print axioms SerrePositivity.KST.SConstruction.pointwiseDiagramPushoutApex_evaluate
#check @SerrePositivity.KST.SConstruction.curry_identitySpan
#print axioms SerrePositivity.KST.SConstruction.curry_identitySpan
#check @SerrePositivity.KST.SConstruction.spanFamily_constant_right
#print axioms SerrePositivity.KST.SConstruction.spanFamily_constant_right
#check @SerrePositivity.KST.SConstruction.spanFamily_constant_left
#print axioms SerrePositivity.KST.SConstruction.spanFamily_constant_left
#check @SerrePositivity.KST.SConstruction.cofiberProjection_source
#print axioms SerrePositivity.KST.SConstruction.cofiberProjection_source
#check @SerrePositivity.KST.SConstruction.mcCarthySpan_source
#print axioms SerrePositivity.KST.SConstruction.mcCarthySpan_source
#check @SerrePositivity.KST.SConstruction.mcCarthyLambdaMu_quotient
#print axioms SerrePositivity.KST.SConstruction.mcCarthyLambdaMu_quotient
#check @SerrePositivity.KST.SConstruction.mcCarthySpan_quotient
#print axioms SerrePositivity.KST.SConstruction.mcCarthySpan_quotient
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoRaw_source
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoRaw_source
#check @SerrePositivity.KST.SConstruction.mcCarthyRho_source
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRho_source
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoRaw_quotient
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoRaw_quotient
#check @SerrePositivity.KST.SConstruction.mcCarthyRho_quotient
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRho_quotient
#check @SerrePositivity.KST.SConstruction.mcCarthyFiberDiagram
#print axioms SerrePositivity.KST.SConstruction.mcCarthyFiberDiagram
#check @SerrePositivity.KST.SConstruction.mcCarthyFiberParameter
#print axioms SerrePositivity.KST.SConstruction.mcCarthyFiberParameter
#check @SerrePositivity.KST.SConstruction.mcCarthyFiberDiagram_source
#print axioms SerrePositivity.KST.SConstruction.mcCarthyFiberDiagram_source
#check @SerrePositivity.KST.SConstruction.mcCarthyFiberDiagram_map
#print axioms SerrePositivity.KST.SConstruction.mcCarthyFiberDiagram_map
#check @SerrePositivity.KST.SConstruction.mcCarthyFiberParameter_map
#print axioms SerrePositivity.KST.SConstruction.mcCarthyFiberParameter_map
#check @SerrePositivity.KST.SConstruction.simplexOrder_map
#print axioms SerrePositivity.KST.SConstruction.simplexOrder_map
#check @SerrePositivity.KST.SConstruction.mcCarthyRho_congr
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRho_congr
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiberObjectVertex
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiberObjectVertex
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiberObjectVertex_diagram
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiberObjectVertex_diagram
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiberObjectMap
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiberObjectMap
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiberParameterMap
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiberParameterMap
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiber_condition
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiber_condition
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiberMap
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiberMap
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiberMap_projection
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiberMap_projection
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiberMap_parameter
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiberMap_parameter
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiberObjectMap_zero
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiberObjectMap_zero
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiberParameterMap_endpoint
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiberParameterMap_endpoint
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiberMap_zero
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiberMap_zero
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoTerminal
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoTerminal
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiberHomotopy
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiberHomotopy
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoFiberMap_quotient
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoFiberMap_quotient
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoTerminal_parameter
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoTerminal_parameter
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoTerminal_quotient
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoTerminal_quotient
#check @SerrePositivity.KST.SConstruction.mcCarthyRhoTerminal_source
#print axioms SerrePositivity.KST.SConstruction.mcCarthyRhoTerminal_source

#check @SerrePositivity.KST.SConstruction.exists_relative_initialPrism
#print axioms SerrePositivity.KST.SConstruction.exists_relative_initialPrism
#check @SerrePositivity.KST.SConstruction.fixedSourceArrows
#print axioms SerrePositivity.KST.SConstruction.fixedSourceArrows
#check @SerrePositivity.KST.SConstruction.fixedSourceArrowsι
#print axioms SerrePositivity.KST.SConstruction.fixedSourceArrowsι
#check @SerrePositivity.KST.SConstruction.fixedSourceArrowsTarget
#print axioms SerrePositivity.KST.SConstruction.fixedSourceArrowsTarget
#check @SerrePositivity.KST.SConstruction.fixedSourceArrowsι_source
#print axioms SerrePositivity.KST.SConstruction.fixedSourceArrowsι_source
#check @SerrePositivity.KST.SConstruction.fixedSourceArrowsTarget_trivialKanFibration
#print axioms SerrePositivity.KST.SConstruction.fixedSourceArrowsTarget_trivialKanFibration
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibers
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibers
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersι
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersι
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersι_source
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersι_source
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersQuotient
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersQuotient
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersInput
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersInput
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersInput_ι
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersInput_ι
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersCanonical
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersCanonical
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersCanonical_source
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersCanonical_source
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersCanonicalInput
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersCanonicalInput
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersCanonicalInput_ι
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersCanonicalInput_ι
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersRightPrism
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersRightPrism
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersRightPrism_zero
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersRightPrism_zero
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersRightPrism_one
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersRightPrism_one
#check @SerrePositivity.KST.SConstruction.zeroSourceThetaInput
#print axioms SerrePositivity.KST.SConstruction.zeroSourceThetaInput
#check @SerrePositivity.KST.SConstruction.zeroSourceThetaInput_zero
#print axioms SerrePositivity.KST.SConstruction.zeroSourceThetaInput_zero
#check @SerrePositivity.KST.SConstruction.zeroSourceThetaInput_one
#print axioms SerrePositivity.KST.SConstruction.zeroSourceThetaInput_one
#check @SerrePositivity.KST.SConstruction.zeroSourceThetaInput_target
#print axioms SerrePositivity.KST.SConstruction.zeroSourceThetaInput_target
#check @SerrePositivity.KST.SConstruction.zeroSourceTheta
#print axioms SerrePositivity.KST.SConstruction.zeroSourceTheta
#check @SerrePositivity.KST.SConstruction.zeroSourceTheta_zero
#print axioms SerrePositivity.KST.SConstruction.zeroSourceTheta_zero
#check @SerrePositivity.KST.SConstruction.zeroSourceTheta_one
#print axioms SerrePositivity.KST.SConstruction.zeroSourceTheta_one
#check @SerrePositivity.KST.SConstruction.zeroSourceTheta_projection
#print axioms SerrePositivity.KST.SConstruction.zeroSourceTheta_projection
#check @SerrePositivity.KST.SConstruction.zeroSourceTheta_source
#print axioms SerrePositivity.KST.SConstruction.zeroSourceTheta_source
#check @SerrePositivity.KST.SConstruction.uncurry_vertex_restriction
#print axioms SerrePositivity.KST.SConstruction.uncurry_vertex_restriction
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersRightPrism_vertex
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersRightPrism_vertex
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersRight_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersRight_isIso
#check @SerrePositivity.KST.SConstruction.zeroSourceCofibersRightPrism_isInvertible
#print axioms SerrePositivity.KST.SConstruction.zeroSourceCofibersRightPrism_isInvertible
#check @SerrePositivity.KST.SConstruction.zeroSourceThetaInput_isInvertible
#print axioms SerrePositivity.KST.SConstruction.zeroSourceThetaInput_isInvertible
#check @SerrePositivity.KST.SConstruction.zeroSourceTheta_isInvertible
#print axioms SerrePositivity.KST.SConstruction.zeroSourceTheta_isInvertible
#check @SerrePositivity.KST.SConstruction.zeroSourceThetaHomotopy
#print axioms SerrePositivity.KST.SConstruction.zeroSourceThetaHomotopy
#check @SerrePositivity.KST.SConstruction.zeroSourceThetaHomotopy_isInvertible
#print axioms SerrePositivity.KST.SConstruction.zeroSourceThetaHomotopy_isInvertible
#check @SerrePositivity.KST.SConstruction.zeroSourceTheta_variableTime_isGapped
#print axioms SerrePositivity.KST.SConstruction.zeroSourceTheta_variableTime_isGapped
#check @SerrePositivity.KST.SConstruction.zeroSourceTheta_variableTime_source
#print axioms SerrePositivity.KST.SConstruction.zeroSourceTheta_variableTime_source
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaDiagram
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaDiagram
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaDiagram_ι
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaDiagram_ι
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaDiagram_map
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaDiagram_map
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaDiagram_isGapped
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaDiagram_isGapped
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaObjectVertex
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaObjectVertex
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaObjectVertex_diagram
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaObjectVertex_diagram
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaObjectMap
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaObjectMap
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaFiber_condition
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaFiber_condition
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaFiberMap
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaFiberMap
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaFiberMap_projection
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaFiberMap_projection
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaFiberMap_parameter
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaFiberMap_parameter
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaDiagram_quotient
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaDiagram_quotient
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaObjectMap_zero
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaObjectMap_zero
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaObjectMap_one
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaObjectMap_one
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaFiberMap_zero
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaFiberMap_zero
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaFiberMap_one
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaFiberMap_one
#check @SerrePositivity.KST.SConstruction.mcCarthyThetaFiberHomotopy
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaFiberHomotopy
#check @SerrePositivity.KST.SConstruction.mcCarthyFiber_retraction_localized
#print axioms SerrePositivity.KST.SConstruction.mcCarthyFiber_retraction_localized
#check @SerrePositivity.KST.SConstruction.cofiberLeftFiberQuotient_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.cofiberLeftFiberQuotient_localized_isIso

#check @SerrePositivity.KST.SConstruction.simplexFiberDiagramMap
#print axioms SerrePositivity.KST.SConstruction.simplexFiberDiagramMap

#check @SerrePositivity.KST.SConstruction.simplexFiberDiagramMap_projection
#print axioms SerrePositivity.KST.SConstruction.simplexFiberDiagramMap_projection

#check @SerrePositivity.KST.SConstruction.simplexFiberDiagramMap_parameter
#print axioms SerrePositivity.KST.SConstruction.simplexFiberDiagramMap_parameter

#check @SerrePositivity.KST.SConstruction.simplexFiberDiagram
#print axioms SerrePositivity.KST.SConstruction.simplexFiberDiagram

#check @SerrePositivity.KST.SConstruction.simplexFiberProjection
#print axioms SerrePositivity.KST.SConstruction.simplexFiberProjection

#check @SerrePositivity.KST.SConstruction.simplexFiberPostcomp
#print axioms SerrePositivity.KST.SConstruction.simplexFiberPostcomp

#check @SerrePositivity.KST.SConstruction.elementsResolution
#print axioms SerrePositivity.KST.SConstruction.elementsResolution

#check @SerrePositivity.KST.SConstruction.elementsResolutionMap
#print axioms SerrePositivity.KST.SConstruction.elementsResolutionMap

#check @SerrePositivity.KST.SConstruction.elementsResolution_obj
#print axioms SerrePositivity.KST.SConstruction.elementsResolution_obj

#check @SerrePositivity.KST.SConstruction.elementsResolutionMap_app
#print axioms SerrePositivity.KST.SConstruction.elementsResolutionMap_app

#check @SerrePositivity.KST.SConstruction.fiberResolutionCoefficient
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionCoefficient

#check @SerrePositivity.KST.SConstruction.fiberResolutionCategory
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionCategory

#check @SerrePositivity.KST.SConstruction.fiberResolutionValue
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionValue

#check @SerrePositivity.KST.SConstruction.fiberResolutionParameter
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionParameter

#check @SerrePositivity.KST.SConstruction.fiberResolution_condition
#print axioms SerrePositivity.KST.SConstruction.fiberResolution_condition

#check @SerrePositivity.KST.SConstruction.fiberResolutionValue_map
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionValue_map

#check @SerrePositivity.KST.SConstruction.fiberResolutionParameter_map
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionParameter_map

#check @SerrePositivity.KST.SConstruction.fiberResolutionCanonicalSimplex
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionCanonicalSimplex

#check @SerrePositivity.KST.SConstruction.fiberResolutionCanonicalSimplex_projection
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionCanonicalSimplex_projection

#check @SerrePositivity.KST.SConstruction.fiberResolutionCanonicalSimplex_parameter
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionCanonicalSimplex_parameter

#check @SerrePositivity.KST.SConstruction.fiberResolutionCanonical
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionCanonical

#check @SerrePositivity.KST.SConstruction.fiberResolutionCanonical_value
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionCanonical_value

#check @SerrePositivity.KST.SConstruction.fiberResolutionCanonical_parameter
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionCanonical_parameter

#check @SerrePositivity.KST.SConstruction.fiberResolutionCanonicalBaseArrow
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionCanonicalBaseArrow

#check @SerrePositivity.KST.SConstruction.fiberResolutionCanonicalBaseArrow_map
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionCanonicalBaseArrow_map

#check @SerrePositivity.KST.SConstruction.fiberResolutionCanonicalArrow
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionCanonicalArrow

#check @SerrePositivity.KST.SConstruction.fiberResolutionCanonicalArrow_unique
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionCanonicalArrow_unique

#check @SerrePositivity.KST.SConstruction.resolutionNerveMap
#print axioms SerrePositivity.KST.SConstruction.resolutionNerveMap

#check @SerrePositivity.KST.SConstruction.fiberResolutionValueFunctor
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionValueFunctor

#check @SerrePositivity.KST.SConstruction.fiberResolutionSectionFunctor
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionSectionFunctor

#check @SerrePositivity.KST.SConstruction.fiberResolutionContraction
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionContraction

#check @SerrePositivity.KST.SConstruction.fiberResolutionSectionValueIso
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionSectionValueIso

#check @SerrePositivity.KST.SConstruction.fiberResolutionValueFunctor_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionValueFunctor_localized_isIso

#check @SerrePositivity.KST.SConstruction.discreteNerveConstantIso
#print axioms SerrePositivity.KST.SConstruction.discreteNerveConstantIso

#check @SerrePositivity.KST.SConstruction.fiberResolutionRowAugmentation
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionRowAugmentation

#check @SerrePositivity.KST.SConstruction.fiberResolutionRowAugmentation_eq
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionRowAugmentation_eq

#check @SerrePositivity.KST.SConstruction.fiberResolutionRowAugmentation_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionRowAugmentation_localized_isIso

#check @SerrePositivity.KST.SConstruction.fiberResolutionRowsAugmentation
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionRowsAugmentation

#check @SerrePositivity.KST.SConstruction.constantRowsDiagonalIso
#print axioms SerrePositivity.KST.SConstruction.constantRowsDiagonalIso

#check @SerrePositivity.KST.SConstruction.fiberResolutionAugmentation
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionAugmentation

#check @SerrePositivity.KST.SConstruction.fiberResolutionAugmentation_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.fiberResolutionAugmentation_localized_isIso

#check @SerrePositivity.KST.SConstruction.oppositeLabelledChainLift
#print axioms SerrePositivity.KST.SConstruction.oppositeLabelledChainLift

#check @SerrePositivity.KST.SConstruction.oppositeLabelledChain_reconstruct
#print axioms SerrePositivity.KST.SConstruction.oppositeLabelledChain_reconstruct

#check @SerrePositivity.KST.SConstruction.oppositeLabelledChainEquiv
#print axioms SerrePositivity.KST.SConstruction.oppositeLabelledChainEquiv

#check @SerrePositivity.KST.SConstruction.coefficientCoproduct
#print axioms SerrePositivity.KST.SConstruction.coefficientCoproduct

#check @SerrePositivity.KST.SConstruction.coefficientCoproductInclusion
#print axioms SerrePositivity.KST.SConstruction.coefficientCoproductInclusion

#check @SerrePositivity.KST.SConstruction.coefficientCoproductCofan
#print axioms SerrePositivity.KST.SConstruction.coefficientCoproductCofan

#check @SerrePositivity.KST.SConstruction.coefficientCoproductIsColimit
#print axioms SerrePositivity.KST.SConstruction.coefficientCoproductIsColimit

#check @SerrePositivity.KST.SConstruction.coefficientCoproductMap
#print axioms SerrePositivity.KST.SConstruction.coefficientCoproductMap

#check @SerrePositivity.KST.SConstruction.coefficientCoproductMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.coefficientCoproductMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.elementsResolutionRowIso
#print axioms SerrePositivity.KST.SConstruction.elementsResolutionRowIso

#check @SerrePositivity.KST.SConstruction.elementsResolutionRowIso_naturality
#print axioms SerrePositivity.KST.SConstruction.elementsResolutionRowIso_naturality

#check @SerrePositivity.KST.SConstruction.elementsResolutionRowMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.elementsResolutionRowMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.elementsResolutionMap_diagonal_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.elementsResolutionMap_diagonal_localized_isIso

#check @SerrePositivity.KST.SConstruction.constantElementsResolutionComparison
#print axioms SerrePositivity.KST.SConstruction.constantElementsResolutionComparison

#check @SerrePositivity.KST.SConstruction.constantElementsResolutionComparison_bijective
#print axioms SerrePositivity.KST.SConstruction.constantElementsResolutionComparison_bijective

#check @SerrePositivity.KST.SConstruction.constantElementsResolutionIso
#print axioms SerrePositivity.KST.SConstruction.constantElementsResolutionIso

#check @SerrePositivity.KST.SConstruction.tensorCoefficientDiagram
#print axioms SerrePositivity.KST.SConstruction.tensorCoefficientDiagram

#check @SerrePositivity.KST.SConstruction.tensorCoefficientProjection
#print axioms SerrePositivity.KST.SConstruction.tensorCoefficientProjection

#check @SerrePositivity.KST.SConstruction.tensorElementsResolutionComparison
#print axioms SerrePositivity.KST.SConstruction.tensorElementsResolutionComparison

#check @SerrePositivity.KST.SConstruction.tensorElementsResolutionEquiv
#print axioms SerrePositivity.KST.SConstruction.tensorElementsResolutionEquiv

#check @SerrePositivity.KST.SConstruction.tensorElementsResolutionComparison_eq
#print axioms SerrePositivity.KST.SConstruction.tensorElementsResolutionComparison_eq

#check @SerrePositivity.KST.SConstruction.tensorElementsResolutionIso
#print axioms SerrePositivity.KST.SConstruction.tensorElementsResolutionIso

#check @SerrePositivity.KST.SConstruction.identitySimplexFiberSection
#print axioms SerrePositivity.KST.SConstruction.identitySimplexFiberSection

#check @SerrePositivity.KST.SConstruction.identitySimplexFiberIso
#print axioms SerrePositivity.KST.SConstruction.identitySimplexFiberIso

#check @SerrePositivity.KST.SConstruction.identitySimplexFiber_toUnit_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.identitySimplexFiber_toUnit_localized_isIso

#check @SerrePositivity.KST.SConstruction.identitySimplexFiber_snd_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.identitySimplexFiber_snd_localized_isIso

#check @SerrePositivity.KST.SConstruction.simplexFiberIdentityMap
#print axioms SerrePositivity.KST.SConstruction.simplexFiberIdentityMap

#check @SerrePositivity.KST.SConstruction.simplexFiberIdentityComparison
#print axioms SerrePositivity.KST.SConstruction.simplexFiberIdentityComparison

#check @SerrePositivity.KST.SConstruction.simplexFiberProductComparison
#print axioms SerrePositivity.KST.SConstruction.simplexFiberProductComparison

#check @SerrePositivity.KST.SConstruction.simplexFiberProductComparison_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.simplexFiberProductComparison_localized_isIso

#check @SerrePositivity.KST.SConstruction.simplexFiberResolutionProductMap
#print axioms SerrePositivity.KST.SConstruction.simplexFiberResolutionProductMap

#check @SerrePositivity.KST.SConstruction.simplexFiberResolutionProductMap_eq
#print axioms SerrePositivity.KST.SConstruction.simplexFiberResolutionProductMap_eq

#check @SerrePositivity.KST.SConstruction.simplexFiberResolutionProductMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.simplexFiberResolutionProductMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.simplicialProductQuillenA
#print axioms SerrePositivity.KST.SConstruction.simplicialProductQuillenA

#check @SerrePositivity.KST.SConstruction.objectSAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.objectSAdditivityMap

#check @SerrePositivity.KST.SConstruction.objectSAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.objectSAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.coreSRealizationFunctor
#print axioms SerrePositivity.KST.SConstruction.coreSRealizationFunctor

#check @SerrePositivity.KST.SConstruction.objectCoreRealizationComparison
#print axioms SerrePositivity.KST.SConstruction.objectCoreRealizationComparison

#check @SerrePositivity.KST.SConstruction.coreSAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.coreSAdditivityMap

#check @SerrePositivity.KST.SConstruction.objectCoreAdditivity_commute
#print axioms SerrePositivity.KST.SConstruction.objectCoreAdditivity_commute

#check @SerrePositivity.KST.SConstruction.objectCoreComparison_tensor_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.objectCoreComparison_tensor_localized_isIso

#check @SerrePositivity.KST.SConstruction.coreSAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.coreSAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.internalHomSwap_evaluate_right
#print axioms SerrePositivity.KST.SConstruction.internalHomSwap_evaluate_right

#check @SerrePositivity.KST.SConstruction.internalHomSwap_twice
#print axioms SerrePositivity.KST.SConstruction.internalHomSwap_twice

#check @SerrePositivity.KST.SConstruction.sCofiberRawTranspose
#print axioms SerrePositivity.KST.SConstruction.sCofiberRawTranspose

#check @SerrePositivity.KST.SConstruction.sCofiberRawTranspose_vertex
#print axioms SerrePositivity.KST.SConstruction.sCofiberRawTranspose_vertex

#check @SerrePositivity.KST.SConstruction.sCofiberRawTranspose_gapped
#print axioms SerrePositivity.KST.SConstruction.sCofiberRawTranspose_gapped

#check @SerrePositivity.KST.SConstruction.sCofiberTransposeSquare
#print axioms SerrePositivity.KST.SConstruction.sCofiberTransposeSquare

#check @SerrePositivity.KST.SConstruction.sCofiberTransposeSquare_ι
#print axioms SerrePositivity.KST.SConstruction.sCofiberTransposeSquare_ι

#check @SerrePositivity.KST.SConstruction.gappedVertex_isZero_of_pointwise
#print axioms SerrePositivity.KST.SConstruction.gappedVertex_isZero_of_pointwise

#check @SerrePositivity.KST.SConstruction.gappedSquare_cofiber_iff_pointwise
#print axioms SerrePositivity.KST.SConstruction.gappedSquare_cofiber_iff_pointwise

#check @SerrePositivity.KST.SConstruction.sCofiberTransposeSquare_vertex_ι
#print axioms SerrePositivity.KST.SConstruction.sCofiberTransposeSquare_vertex_ι

#check @SerrePositivity.KST.SConstruction.sCofiberTransposeSquare_isCofiber
#print axioms SerrePositivity.KST.SConstruction.sCofiberTransposeSquare_isCofiber

#check @SerrePositivity.KST.SConstruction.sCofiberComparison
#print axioms SerrePositivity.KST.SConstruction.sCofiberComparison

#check @SerrePositivity.KST.SConstruction.sCofiberComparison_ι
#print axioms SerrePositivity.KST.SConstruction.sCofiberComparison_ι

#check @SerrePositivity.KST.SConstruction.sCofiberComparison_evaluation
#print axioms SerrePositivity.KST.SConstruction.sCofiberComparison_evaluation

#check @SerrePositivity.KST.SConstruction.isPushoutSquare_fullSubcomplex_of_ambient
#print axioms SerrePositivity.KST.SConstruction.isPushoutSquare_fullSubcomplex_of_ambient

#check @SerrePositivity.KST.SConstruction.IsGapped.of_fullSubcomplex
#print axioms SerrePositivity.KST.SConstruction.IsGapped.of_fullSubcomplex

#check @SerrePositivity.KST.SConstruction.sCofiberRawInverse
#print axioms SerrePositivity.KST.SConstruction.sCofiberRawInverse

#check @SerrePositivity.KST.SConstruction.sCofiberRawInverse_vertex
#print axioms SerrePositivity.KST.SConstruction.sCofiberRawInverse_vertex

#check @SerrePositivity.KST.SConstruction.sCofiberRawInverse_cofiber
#print axioms SerrePositivity.KST.SConstruction.sCofiberRawInverse_cofiber

#check @SerrePositivity.KST.SConstruction.sCofiberInverseDiagram
#print axioms SerrePositivity.KST.SConstruction.sCofiberInverseDiagram

#check @SerrePositivity.KST.SConstruction.sCofiberInverseDiagram_ι
#print axioms SerrePositivity.KST.SConstruction.sCofiberInverseDiagram_ι

#check @SerrePositivity.KST.SConstruction.sCofiberInverseDiagram_vertex_ι
#print axioms SerrePositivity.KST.SConstruction.sCofiberInverseDiagram_vertex_ι

#check @SerrePositivity.KST.SConstruction.sCofiberInverseDiagram_isGapped
#print axioms SerrePositivity.KST.SConstruction.sCofiberInverseDiagram_isGapped

#check @SerrePositivity.KST.SConstruction.sCofiberInverse
#print axioms SerrePositivity.KST.SConstruction.sCofiberInverse

#check @SerrePositivity.KST.SConstruction.sCofiberInverse_ι
#print axioms SerrePositivity.KST.SConstruction.sCofiberInverse_ι

#check @SerrePositivity.KST.SConstruction.sCofiberComparison_double_ι
#print axioms SerrePositivity.KST.SConstruction.sCofiberComparison_double_ι

#check @SerrePositivity.KST.SConstruction.sCofiberInverse_double_ι
#print axioms SerrePositivity.KST.SConstruction.sCofiberInverse_double_ι

#check @SerrePositivity.KST.SConstruction.inverse_comp_of_commuting_mono
#print axioms SerrePositivity.KST.SConstruction.inverse_comp_of_commuting_mono

#check @SerrePositivity.KST.SConstruction.sCofiberComparison_inverse
#print axioms SerrePositivity.KST.SConstruction.sCofiberComparison_inverse

#check @SerrePositivity.KST.SConstruction.sCofiberInverse_comparison
#print axioms SerrePositivity.KST.SConstruction.sCofiberInverse_comparison

#check @SerrePositivity.KST.SConstruction.sCofiberIso
#print axioms SerrePositivity.KST.SConstruction.sCofiberIso

#check @SerrePositivity.KST.SConstruction.sCofiberStableIso
#print axioms SerrePositivity.KST.SConstruction.sCofiberStableIso

#check @SerrePositivity.KST.SConstruction.sCofiberStableIso_evaluation
#print axioms SerrePositivity.KST.SConstruction.sCofiberStableIso_evaluation

#check @SerrePositivity.KST.SConstruction.sCofiberStableIso_subobject
#print axioms SerrePositivity.KST.SConstruction.sCofiberStableIso_subobject

#check @SerrePositivity.KST.SConstruction.sCofiberStableIso_quotient
#print axioms SerrePositivity.KST.SConstruction.sCofiberStableIso_quotient

#check @SerrePositivity.KST.SConstruction.sCofiberStableIso_realization_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.sCofiberStableIso_realization_localized_isIso

#check @SerrePositivity.KST.SConstruction.sCofiberStableIso_pair
#print axioms SerrePositivity.KST.SConstruction.sCofiberStableIso_pair

#check @SerrePositivity.KST.SConstruction.coreSRowAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.coreSRowAdditivityMap

#check @SerrePositivity.KST.SConstruction.coreSRowAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.coreSRowAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.objectSRowAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.objectSRowAdditivityMap

#check @SerrePositivity.KST.SConstruction.objectSRowAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.objectSRowAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.diagonalTensorIso
#print axioms SerrePositivity.KST.SConstruction.diagonalTensorIso

#check @SerrePositivity.KST.SConstruction.diagonalTensorIso_pair
#print axioms SerrePositivity.KST.SConstruction.diagonalTensorIso_pair

#check @SerrePositivity.KST.SConstruction.coreSingleRealizationIso
#print axioms SerrePositivity.KST.SConstruction.coreSingleRealizationIso

#check @SerrePositivity.KST.SConstruction.coreSingleRealizationIso_naturality
#print axioms SerrePositivity.KST.SConstruction.coreSingleRealizationIso_naturality

#check @SerrePositivity.KST.SConstruction.multiRealizationAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.multiRealizationAdditivityMap

#check @SerrePositivity.KST.SConstruction.coreSingleRealizationIso_additivity
#print axioms SerrePositivity.KST.SConstruction.coreSingleRealizationIso_additivity

#check @SerrePositivity.KST.SConstruction.multiRealizationAdditivityMap_one_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.multiRealizationAdditivityMap_one_localized_isIso

#check @SerrePositivity.KST.SConstruction.iteratedSAdditivityDiagram
#print axioms SerrePositivity.KST.SConstruction.iteratedSAdditivityDiagram

#check @SerrePositivity.KST.SConstruction.iteratedSAdditivityDiagram_app_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.iteratedSAdditivityDiagram_app_localized_isIso

#check @SerrePositivity.KST.SConstruction.iteratedSAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.iteratedSAdditivityMap

#check @SerrePositivity.KST.SConstruction.iteratedSAdditivityMap_eq
#print axioms SerrePositivity.KST.SConstruction.iteratedSAdditivityMap_eq

#check @SerrePositivity.KST.SConstruction.iteratedSAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.iteratedSAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.iteratedSRealizationCoordinateIso_additivity
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealizationCoordinateIso_additivity

#check @SerrePositivity.KST.SConstruction.multiRealizationAdditivityMap_step_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.multiRealizationAdditivityMap_step_localized_isIso

#check @SerrePositivity.KST.SConstruction.multiRealizationAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.multiRealizationAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.multiRealizationAdditivityMap_localized_isIso_of_pos
#print axioms SerrePositivity.KST.SConstruction.multiRealizationAdditivityMap_localized_isIso_of_pos

#check @SerrePositivity.KST.SConstruction.ihom_map_preservesCofiberData
#print axioms SerrePositivity.KST.SConstruction.ihom_map_preservesCofiberData

#check @SerrePositivity.KST.SConstruction.cofiberPostcomp_vertex
#print axioms SerrePositivity.KST.SConstruction.cofiberPostcomp_vertex

#check @SerrePositivity.KST.SConstruction.cofiberPostcomp
#print axioms SerrePositivity.KST.SConstruction.cofiberPostcomp

#check @SerrePositivity.KST.SConstruction.cofiberPostcomp_ι
#print axioms SerrePositivity.KST.SConstruction.cofiberPostcomp_ι

#check @SerrePositivity.KST.SConstruction.cofiberPostcomp_evaluation
#print axioms SerrePositivity.KST.SConstruction.cofiberPostcomp_evaluation

#check @SerrePositivity.KST.SConstruction.preservesCofiberData_fullSubcomplex_of_comp
#print axioms SerrePositivity.KST.SConstruction.preservesCofiberData_fullSubcomplex_of_comp

#check @SerrePositivity.KST.SConstruction.cofiberPostcomp_preservesCofiberData
#print axioms SerrePositivity.KST.SConstruction.cofiberPostcomp_preservesCofiberData

#check @SerrePositivity.KST.SConstruction.cofiberPostcomp_id
#print axioms SerrePositivity.KST.SConstruction.cofiberPostcomp_id

#check @SerrePositivity.KST.SConstruction.cofiberPostcomp_comp
#print axioms SerrePositivity.KST.SConstruction.cofiberPostcomp_comp

#check @SerrePositivity.KST.SConstruction.cofiberEndofunctor
#print axioms SerrePositivity.KST.SConstruction.cofiberEndofunctor

#check @SerrePositivity.KST.SConstruction.cofiberEvaluationNat
#print axioms SerrePositivity.KST.SConstruction.cofiberEvaluationNat

#check @SerrePositivity.KST.SConstruction.cofiberSubobjectNat
#print axioms SerrePositivity.KST.SConstruction.cofiberSubobjectNat

#check @SerrePositivity.KST.SConstruction.cofiberQuotientNat
#print axioms SerrePositivity.KST.SConstruction.cofiberQuotientNat

#check @SerrePositivity.KST.SConstruction.cofiberPair_naturality
#print axioms SerrePositivity.KST.SConstruction.cofiberPair_naturality

#check @SerrePositivity.KST.SConstruction.multiRealizationAdditivityNat
#print axioms SerrePositivity.KST.SConstruction.multiRealizationAdditivityNat

#check @SerrePositivity.KST.SConstruction.multiRealizationAdditivityLocalizedIso
#print axioms SerrePositivity.KST.SConstruction.multiRealizationAdditivityLocalizedIso

#check @SerrePositivity.KST.SConstruction.multiRealizationAdditivityLocalizedIso_app
#print axioms SerrePositivity.KST.SConstruction.multiRealizationAdditivityLocalizedIso_app

#check @SerrePositivity.KST.SConstruction.sTwoCofiberComparison_evaluation
#print axioms SerrePositivity.KST.SConstruction.sTwoCofiberComparison_evaluation

#check @SerrePositivity.KST.SConstruction.sTwoRealizationAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.sTwoRealizationAdditivityMap

#check @SerrePositivity.KST.SConstruction.sTwoRealizationAdditivityMap_eq
#print axioms SerrePositivity.KST.SConstruction.sTwoRealizationAdditivityMap_eq

#check @SerrePositivity.KST.SConstruction.sTwoRealizationAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.sTwoRealizationAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.terminalBoundaryLifting_reflect_of_boundary_lifting
#print axioms SerrePositivity.KST.SConstruction.terminalBoundaryLifting_reflect_of_boundary_lifting

#check @SerrePositivity.KST.SConstruction.isLimitCone_fullSubcomplex_of_ambient
#print axioms SerrePositivity.KST.SConstruction.isLimitCone_fullSubcomplex_of_ambient

#check @SerrePositivity.KST.SConstruction.isPullbackSquare_fullSubcomplex_of_ambient
#print axioms SerrePositivity.KST.SConstruction.isPullbackSquare_fullSubcomplex_of_ambient

#check @SerrePositivity.KST.SConstruction.ClosedStablePredicate
#print axioms SerrePositivity.KST.SConstruction.ClosedStablePredicate

#check @SerrePositivity.KST.SConstruction.closedSubcategory
#print axioms SerrePositivity.KST.SConstruction.closedSubcategory

#check @SerrePositivity.KST.SConstruction.closedSubcategory_quasicategory
#print axioms SerrePositivity.KST.SConstruction.closedSubcategory_quasicategory

#check @SerrePositivity.KST.SConstruction.closedSubcategory_vertex
#print axioms SerrePositivity.KST.SConstruction.closedSubcategory_vertex

#check @SerrePositivity.KST.SConstruction.square_vertices_of_corners
#print axioms SerrePositivity.KST.SConstruction.square_vertices_of_corners

#check @SerrePositivity.KST.SConstruction.fullSubcategoryVertex
#print axioms SerrePositivity.KST.SConstruction.fullSubcategoryVertex

#check @SerrePositivity.KST.SConstruction.closedSubcategory_hasZeroVertex
#print axioms SerrePositivity.KST.SConstruction.closedSubcategory_hasZeroVertex

#check @SerrePositivity.KST.SConstruction.squareBottomEdge_eq_of_pushoutSpan_eq
#print axioms SerrePositivity.KST.SConstruction.squareBottomEdge_eq_of_pushoutSpan_eq

#check @SerrePositivity.KST.SConstruction.squareLeftEdge_eq_of_pushoutSpan_eq
#print axioms SerrePositivity.KST.SConstruction.squareLeftEdge_eq_of_pushoutSpan_eq

#check @SerrePositivity.KST.SConstruction.square_initial_corners_of_span
#print axioms SerrePositivity.KST.SConstruction.square_initial_corners_of_span

#check @SerrePositivity.KST.SConstruction.exists_closedSubcategory_pushoutSquare
#print axioms SerrePositivity.KST.SConstruction.exists_closedSubcategory_pushoutSquare

#check @SerrePositivity.KST.SConstruction.closedSubcategoryInclusion_preservesPushout
#print axioms SerrePositivity.KST.SConstruction.closedSubcategoryInclusion_preservesPushout

#check @SerrePositivity.KST.SConstruction.closedSubcategoryInclusion_preservesZero
#print axioms SerrePositivity.KST.SConstruction.closedSubcategoryInclusion_preservesZero

#check @SerrePositivity.KST.SConstruction.closedSubcategoryInclusion_preservesSConstructionData
#print axioms SerrePositivity.KST.SConstruction.closedSubcategoryInclusion_preservesSConstructionData

#check @SerrePositivity.KST.SConstruction.exists_pullbackSquare_of_zero_corner
#print axioms SerrePositivity.KST.SConstruction.exists_pullbackSquare_of_zero_corner

#check @SerrePositivity.KST.SConstruction.square_final_corners_of_cospan
#print axioms SerrePositivity.KST.SConstruction.square_final_corners_of_cospan

#check @SerrePositivity.KST.SConstruction.exists_closedSubcategory_pullbackSquare
#print axioms SerrePositivity.KST.SConstruction.exists_closedSubcategory_pullbackSquare

#check @SerrePositivity.KST.SConstruction.closedSubcategoryInclusion_preservesFiber
#print axioms SerrePositivity.KST.SConstruction.closedSubcategoryInclusion_preservesFiber

#check @SerrePositivity.KST.SConstruction.yonedaEdge_source
#print axioms SerrePositivity.KST.SConstruction.yonedaEdge_source

#check @SerrePositivity.KST.SConstruction.yonedaEdge_target
#print axioms SerrePositivity.KST.SConstruction.yonedaEdge_target

#check @SerrePositivity.KST.SConstruction.square_bottom_vertices
#print axioms SerrePositivity.KST.SConstruction.square_bottom_vertices

#check @SerrePositivity.KST.SConstruction.square_right_vertices
#print axioms SerrePositivity.KST.SConstruction.square_right_vertices

#check @SerrePositivity.KST.SConstruction.closedSubcategory_cofiber_nonempty
#print axioms SerrePositivity.KST.SConstruction.closedSubcategory_cofiber_nonempty

#check @SerrePositivity.KST.SConstruction.closedSubcategory_fiber_nonempty
#print axioms SerrePositivity.KST.SConstruction.closedSubcategory_fiber_nonempty

#check @SerrePositivity.KST.SConstruction.closedSubcategory_isStable
#print axioms SerrePositivity.KST.SConstruction.closedSubcategory_isStable

#check @SerrePositivity.KST.SConstruction.closedStableModel
#print axioms SerrePositivity.KST.SConstruction.closedStableModel

#check @SerrePositivity.KST.SConstruction.closedStableInclusion
#print axioms SerrePositivity.KST.SConstruction.closedStableInclusion

#check @SerrePositivity.KST.SConstruction.PreservesCofiberData.isExactFunctor
#print axioms SerrePositivity.KST.SConstruction.PreservesCofiberData.isExactFunctor

#check @SerrePositivity.KST.SConstruction.ClosedStablePredicate.comap
#print axioms SerrePositivity.KST.SConstruction.ClosedStablePredicate.comap

#check @SerrePositivity.KST.SConstruction.ClosedStablePredicate.inter
#print axioms SerrePositivity.KST.SConstruction.ClosedStablePredicate.inter

#check @SerrePositivity.KST.SConstruction.ClosedStablePredicate.top
#print axioms SerrePositivity.KST.SConstruction.ClosedStablePredicate.top

#check @SerrePositivity.KST.SConstruction.relativeCofiberPredicate
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberPredicate

#check @SerrePositivity.KST.SConstruction.relativeCofiberDiagrams
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberDiagrams

#check @SerrePositivity.KST.SConstruction.relativeCofiberDiagrams_quasicategory
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberDiagrams_quasicategory

#check @SerrePositivity.KST.SConstruction.relativeCofiberDiagrams_isStable
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberDiagrams_isStable

#check @SerrePositivity.KST.SConstruction.relativeCofiberStableModel
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberStableModel

#check @SerrePositivity.KST.SConstruction.relativeCofiberInclusion
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberInclusion

#check @SerrePositivity.KST.SConstruction.relativeCofiber_vertex
#print axioms SerrePositivity.KST.SConstruction.relativeCofiber_vertex

#check @SerrePositivity.KST.SConstruction.relativeCofiberSubobjectMap
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberSubobjectMap

#check @SerrePositivity.KST.SConstruction.relativeCofiberQuotientMap
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberQuotientMap

#check @SerrePositivity.KST.SConstruction.relativeCofiberSubobjectMap_ι
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberSubobjectMap_ι

#check @SerrePositivity.KST.SConstruction.relativeCofiberQuotientMap_ι
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberQuotientMap_ι

#check @SerrePositivity.KST.SConstruction.relativeCofiberSubobject
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberSubobject

#check @SerrePositivity.KST.SConstruction.relativeCofiberQuotient
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberQuotient

#check @SerrePositivity.KST.SConstruction.relativeCofiberSubobject_inclusion
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberSubobject_inclusion

#check @SerrePositivity.KST.SConstruction.relativeCofiberQuotient_inclusion
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberQuotient_inclusion

#check @SerrePositivity.KST.SConstruction.ClosedStablePredicate.predicate
#print axioms SerrePositivity.KST.SConstruction.ClosedStablePredicate.predicate

#check @SerrePositivity.KST.SConstruction.ClosedStablePredicate.of_iso
#print axioms SerrePositivity.KST.SConstruction.ClosedStablePredicate.of_iso

#check @SerrePositivity.KST.SConstruction.ClosedStablePredicate.zero_mem
#print axioms SerrePositivity.KST.SConstruction.ClosedStablePredicate.zero_mem

#check @SerrePositivity.KST.SConstruction.ClosedStablePredicate.pushout_mem
#print axioms SerrePositivity.KST.SConstruction.ClosedStablePredicate.pushout_mem

#check @SerrePositivity.KST.SConstruction.ClosedStablePredicate.pullback_mem
#print axioms SerrePositivity.KST.SConstruction.ClosedStablePredicate.pullback_mem

#check @SerrePositivity.KST.SConstruction.objectSConstructionFunctor_map_injective
#print axioms SerrePositivity.KST.SConstruction.objectSConstructionFunctor_map_injective

#check @SerrePositivity.KST.SConstruction.objectSConstructionFunctor_map_mono
#print axioms SerrePositivity.KST.SConstruction.objectSConstructionFunctor_map_mono

#check @SerrePositivity.KST.SConstruction.ObjectSInClosed
#print axioms SerrePositivity.KST.SConstruction.ObjectSInClosed

#check @SerrePositivity.KST.SConstruction.objectSClosedInclusion_mem
#print axioms SerrePositivity.KST.SConstruction.objectSClosedInclusion_mem

#check @SerrePositivity.KST.SConstruction.objectSClosedVertexLift
#print axioms SerrePositivity.KST.SConstruction.objectSClosedVertexLift

#check @SerrePositivity.KST.SConstruction.objectSClosedVertexLift_diagram
#print axioms SerrePositivity.KST.SConstruction.objectSClosedVertexLift_diagram

#check @SerrePositivity.KST.SConstruction.objectSClosedVertexLift_inclusion
#print axioms SerrePositivity.KST.SConstruction.objectSClosedVertexLift_inclusion

#check @SerrePositivity.KST.SConstruction.ObjectSInClosed.map
#print axioms SerrePositivity.KST.SConstruction.ObjectSInClosed.map

#check @SerrePositivity.KST.SConstruction.closedObjectSSubcomplex
#print axioms SerrePositivity.KST.SConstruction.closedObjectSSubcomplex

#check @SerrePositivity.KST.SConstruction.closedObjectSConstruction
#print axioms SerrePositivity.KST.SConstruction.closedObjectSConstruction

#check @SerrePositivity.KST.SConstruction.closedObjectSInclusion
#print axioms SerrePositivity.KST.SConstruction.closedObjectSInclusion

#check @SerrePositivity.KST.SConstruction.objectSClosedForward
#print axioms SerrePositivity.KST.SConstruction.objectSClosedForward

#check @SerrePositivity.KST.SConstruction.objectSClosedBackward
#print axioms SerrePositivity.KST.SConstruction.objectSClosedBackward

#check @SerrePositivity.KST.SConstruction.objectSClosedIso
#print axioms SerrePositivity.KST.SConstruction.objectSClosedIso

#check @SerrePositivity.KST.SConstruction.objectSClosedForward_inclusion
#print axioms SerrePositivity.KST.SConstruction.objectSClosedForward_inclusion

#check @SerrePositivity.KST.SConstruction.closedObjectSFamily
#print axioms SerrePositivity.KST.SConstruction.closedObjectSFamily

#check @SerrePositivity.KST.SConstruction.objectSClosedBackward_inclusion
#print axioms SerrePositivity.KST.SConstruction.objectSClosedBackward_inclusion

#check @SerrePositivity.KST.SConstruction.objectSClosedFamilyLift
#print axioms SerrePositivity.KST.SConstruction.objectSClosedFamilyLift

#check @SerrePositivity.KST.SConstruction.objectSClosedFamilyLift_inclusion
#print axioms SerrePositivity.KST.SConstruction.objectSClosedFamilyLift_inclusion

#check @SerrePositivity.KST.SConstruction.objectSClosedFamilyLift_unique
#print axioms SerrePositivity.KST.SConstruction.objectSClosedFamilyLift_unique

#check @SerrePositivity.KST.SConstruction.relativeCofiberObjectSubobject_square
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberObjectSubobject_square

#check @SerrePositivity.KST.SConstruction.relativeCofiberObjectQuotient_square
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberObjectQuotient_square

#check @SerrePositivity.KST.SConstruction.relativeCofiberSubobjectLeftFiber
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberSubobjectLeftFiber

#check @SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberQuotient
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberQuotient

#check @SerrePositivity.KST.SConstruction.relativeCofiberBaseSimplex
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberBaseSimplex

#check @SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberForget
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberForget

#check @SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberForget_projection
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberForget_projection

#check @SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberForget_parameter
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberForget_parameter

#check @SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberForget_quotient
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberForget_quotient

#check @SerrePositivity.KST.SConstruction.objectSInRelativeCofiber_iff
#print axioms SerrePositivity.KST.SConstruction.objectSInRelativeCofiber_iff

#check @SerrePositivity.KST.SConstruction.cofiberLeftFiberSubobject_in_closed
#print axioms SerrePositivity.KST.SConstruction.cofiberLeftFiberSubobject_in_closed

#check @SerrePositivity.KST.SConstruction.cofiberLeftFiber_in_relative_iff
#print axioms SerrePositivity.KST.SConstruction.cofiberLeftFiber_in_relative_iff

#check @SerrePositivity.KST.SConstruction.relativeCofiberBaseSimplex_in_closed
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberBaseSimplex_in_closed

#check @SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberForget_quotient_in_closed
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberForget_quotient_in_closed

#check @SerrePositivity.KST.SConstruction.relativeCofiberFiberObjectLift
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberFiberObjectLift

#check @SerrePositivity.KST.SConstruction.relativeCofiberFiberObjectLift_inclusion
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberFiberObjectLift_inclusion

#check @SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberLift
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberLift

#check @SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberLift_forget
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberLift_forget

#check @SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberForget_mono
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberForget_mono

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyRho_quotient_in_closed
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyRho_quotient_in_closed

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyRhoFiberMap
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyRhoFiberMap

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyRhoFiberMap_forget
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyRhoFiberMap_forget

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyRhoFiberMap_zero
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyRhoFiberMap_zero

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyRhoFiberMap_quotient
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyRhoFiberMap_quotient

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyRhoTerminal
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyRhoTerminal

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyRhoHomotopy
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyRhoHomotopy

#check @SerrePositivity.KST.SConstruction.relativeMcCarthySection_quotient_in_closed
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthySection_quotient_in_closed

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyFiberSection
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyFiberSection

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyFiberSection_forget
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyFiberSection_forget

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyFiberSection_quotient
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyFiberSection_quotient

#check @SerrePositivity.KST.SConstruction.ObjectSInClosed.of_functorIso
#print axioms SerrePositivity.KST.SConstruction.ObjectSInClosed.of_functorIso

#check @SerrePositivity.KST.SConstruction.mcCarthyThetaObject_quotient_in_closed
#print axioms SerrePositivity.KST.SConstruction.mcCarthyThetaObject_quotient_in_closed

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyTheta_quotient_in_closed
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyTheta_quotient_in_closed

#check @SerrePositivity.KST.SConstruction.tensorIntervalEndpoint_naturality
#print axioms SerrePositivity.KST.SConstruction.tensorIntervalEndpoint_naturality

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyRhoTerminal_forget
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyRhoTerminal_forget

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyThetaFiberMap
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyThetaFiberMap

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyThetaFiberMap_forget
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyThetaFiberMap_forget

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyThetaFiberMap_zero
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyThetaFiberMap_zero

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyThetaFiberMap_one
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyThetaFiberMap_one

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyThetaHomotopy
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyThetaHomotopy

#check @SerrePositivity.KST.SConstruction.relativeMcCarthyFiber_retraction_localized
#print axioms SerrePositivity.KST.SConstruction.relativeMcCarthyFiber_retraction_localized

#check @SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberQuotient_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberLeftFiberQuotient_localized_isIso

#check @SerrePositivity.KST.SConstruction.relativeObjectSAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.relativeObjectSAdditivityMap

#check @SerrePositivity.KST.SConstruction.relativeObjectSAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.relativeObjectSAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.objectCoreComparisons_tensor_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.objectCoreComparisons_tensor_localized_isIso

#check @SerrePositivity.KST.SConstruction.relativeCoreSAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.relativeCoreSAdditivityMap

#check @SerrePositivity.KST.SConstruction.relativeObjectCoreAdditivity_commute
#print axioms SerrePositivity.KST.SConstruction.relativeObjectCoreAdditivity_commute

#check @SerrePositivity.KST.SConstruction.relativeCoreSAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.relativeCoreSAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.ClosedStablePredicate.iInter
#print axioms SerrePositivity.KST.SConstruction.ClosedStablePredicate.iInter

#check @SerrePositivity.KST.SConstruction.sStableEvaluation
#print axioms SerrePositivity.KST.SConstruction.sStableEvaluation

#check @SerrePositivity.KST.SConstruction.sClosedPredicate
#print axioms SerrePositivity.KST.SConstruction.sClosedPredicate

#check @SerrePositivity.KST.SConstruction.sClosedPredicate_iff
#print axioms SerrePositivity.KST.SConstruction.sClosedPredicate_iff

#check @SerrePositivity.KST.SConstruction.diagramVertex_postcomp
#print axioms SerrePositivity.KST.SConstruction.diagramVertex_postcomp

#check @SerrePositivity.KST.SConstruction.sClosedDiagramLift
#print axioms SerrePositivity.KST.SConstruction.sClosedDiagramLift

#check @SerrePositivity.KST.SConstruction.sClosedDiagramLift_ι
#print axioms SerrePositivity.KST.SConstruction.sClosedDiagramLift_ι

#check @SerrePositivity.KST.SConstruction.sClosedDiagramLift_vertex_ι
#print axioms SerrePositivity.KST.SConstruction.sClosedDiagramLift_vertex_ι

#check @SerrePositivity.KST.SConstruction.sClosedFamilyLift
#print axioms SerrePositivity.KST.SConstruction.sClosedFamilyLift

#check @SerrePositivity.KST.SConstruction.sClosedFamilyLift_inclusion
#print axioms SerrePositivity.KST.SConstruction.sClosedFamilyLift_inclusion

#check @SerrePositivity.KST.SConstruction.sPostcompCofiber_mono
#print axioms SerrePositivity.KST.SConstruction.sPostcompCofiber_mono

#check @SerrePositivity.KST.SConstruction.sClosedInclusion_vertex
#print axioms SerrePositivity.KST.SConstruction.sClosedInclusion_vertex

#check @SerrePositivity.KST.SConstruction.sClosedComparison
#print axioms SerrePositivity.KST.SConstruction.sClosedComparison

#check @SerrePositivity.KST.SConstruction.sClosedComparison_inclusion
#print axioms SerrePositivity.KST.SConstruction.sClosedComparison_inclusion

#check @SerrePositivity.KST.SConstruction.sClosedInverse
#print axioms SerrePositivity.KST.SConstruction.sClosedInverse

#check @SerrePositivity.KST.SConstruction.sClosedInverse_inclusion
#print axioms SerrePositivity.KST.SConstruction.sClosedInverse_inclusion

#check @SerrePositivity.KST.SConstruction.sClosedIso
#print axioms SerrePositivity.KST.SConstruction.sClosedIso

#check @SerrePositivity.KST.SConstruction.sClosedStableIso
#print axioms SerrePositivity.KST.SConstruction.sClosedStableIso

#check @SerrePositivity.KST.SConstruction.sClosedStableIso_inclusion
#print axioms SerrePositivity.KST.SConstruction.sClosedStableIso_inclusion

#check @SerrePositivity.KST.SConstruction.sStableEvaluation_naturality
#print axioms SerrePositivity.KST.SConstruction.sStableEvaluation_naturality

#check @SerrePositivity.KST.SConstruction.closedStableInclusion_cancel
#print axioms SerrePositivity.KST.SConstruction.closedStableInclusion_cancel

#check @SerrePositivity.KST.SConstruction.sCofiberStableIso_subobject_component
#print axioms SerrePositivity.KST.SConstruction.sCofiberStableIso_subobject_component

#check @SerrePositivity.KST.SConstruction.sCofiberStableIso_quotient_component
#print axioms SerrePositivity.KST.SConstruction.sCofiberStableIso_quotient_component

#check @SerrePositivity.KST.SConstruction.sCofiber_relativePredicate_iff
#print axioms SerrePositivity.KST.SConstruction.sCofiber_relativePredicate_iff

#check @SerrePositivity.KST.SConstruction.sRelativeRestrictionIso
#print axioms SerrePositivity.KST.SConstruction.sRelativeRestrictionIso

#check @SerrePositivity.KST.SConstruction.sRelativeRestrictionIso_inclusion
#print axioms SerrePositivity.KST.SConstruction.sRelativeRestrictionIso_inclusion

#check @SerrePositivity.KST.SConstruction.sRelativeCofiberIso
#print axioms SerrePositivity.KST.SConstruction.sRelativeCofiberIso

#check @SerrePositivity.KST.SConstruction.sRelativeCofiberIso_inclusion
#print axioms SerrePositivity.KST.SConstruction.sRelativeCofiberIso_inclusion

#check @SerrePositivity.KST.SConstruction.sRelativeCofiberStableIso
#print axioms SerrePositivity.KST.SConstruction.sRelativeCofiberStableIso

#check @SerrePositivity.KST.SConstruction.sRelativeCofiberStableIso_inclusion
#print axioms SerrePositivity.KST.SConstruction.sRelativeCofiberStableIso_inclusion

#check @SerrePositivity.KST.SConstruction.sRelativeCofiberStableIso_subobject
#print axioms SerrePositivity.KST.SConstruction.sRelativeCofiberStableIso_subobject

#check @SerrePositivity.KST.SConstruction.sRelativeCofiberStableIso_quotient
#print axioms SerrePositivity.KST.SConstruction.sRelativeCofiberStableIso_quotient

#check @SerrePositivity.KST.SConstruction.sRelativeCofiberStableIso_pair
#print axioms SerrePositivity.KST.SConstruction.sRelativeCofiberStableIso_pair

#check @SerrePositivity.KST.SConstruction.relativeRowAdditivity_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.relativeRowAdditivity_localized_isIso

#check @SerrePositivity.KST.SConstruction.relativeCoreSRowAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.relativeCoreSRowAdditivityMap

#check @SerrePositivity.KST.SConstruction.relativeCoreSRowAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.relativeCoreSRowAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.relativeObjectSRowAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.relativeObjectSRowAdditivityMap

#check @SerrePositivity.KST.SConstruction.relativeObjectSRowAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.relativeObjectSRowAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityMap

#check @SerrePositivity.KST.SConstruction.coreSingleRealizationIso_relativeAdditivity
#print axioms SerrePositivity.KST.SConstruction.coreSingleRealizationIso_relativeAdditivity

#check @SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityMap_one_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityMap_one_localized_isIso

#check @SerrePositivity.KST.SConstruction.relativeIteratedSAdditivityDiagram
#print axioms SerrePositivity.KST.SConstruction.relativeIteratedSAdditivityDiagram

#check @SerrePositivity.KST.SConstruction.relativeIteratedSAdditivityDiagram_app_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.relativeIteratedSAdditivityDiagram_app_localized_isIso

#check @SerrePositivity.KST.SConstruction.relativeIteratedSAdditivityMap
#print axioms SerrePositivity.KST.SConstruction.relativeIteratedSAdditivityMap

#check @SerrePositivity.KST.SConstruction.relativeIteratedSAdditivityMap_eq
#print axioms SerrePositivity.KST.SConstruction.relativeIteratedSAdditivityMap_eq

#check @SerrePositivity.KST.SConstruction.relativeIteratedSAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.relativeIteratedSAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.iteratedSRealizationCoordinateIso_relativeAdditivity
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealizationCoordinateIso_relativeAdditivity

#check @SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityMap_step_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityMap_step_localized_isIso

#check @SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityMap_localized_isIso_of_pos
#print axioms SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityMap_localized_isIso_of_pos

#check @SerrePositivity.KST.SConstruction.closedSubcategoryMap
#print axioms SerrePositivity.KST.SConstruction.closedSubcategoryMap

#check @SerrePositivity.KST.SConstruction.closedSubcategoryMap_inclusion
#print axioms SerrePositivity.KST.SConstruction.closedSubcategoryMap_inclusion

#check @SerrePositivity.KST.SConstruction.closedStableMap
#print axioms SerrePositivity.KST.SConstruction.closedStableMap

#check @SerrePositivity.KST.SConstruction.closedStableMap_inclusion
#print axioms SerrePositivity.KST.SConstruction.closedStableMap_inclusion

#check @SerrePositivity.KST.SConstruction.closedStableMap_id
#print axioms SerrePositivity.KST.SConstruction.closedStableMap_id

#check @SerrePositivity.KST.SConstruction.closedStableMap_comp
#print axioms SerrePositivity.KST.SConstruction.closedStableMap_comp

#check @SerrePositivity.KST.SConstruction.RelativeStableModel
#print axioms SerrePositivity.KST.SConstruction.RelativeStableModel

#check @SerrePositivity.KST.SConstruction.relativeStableModelCategory
#print axioms SerrePositivity.KST.SConstruction.relativeStableModelCategory

#check @SerrePositivity.KST.SConstruction.relativeAmbientFunctor
#print axioms SerrePositivity.KST.SConstruction.relativeAmbientFunctor

#check @SerrePositivity.KST.SConstruction.relativeLeftFunctor
#print axioms SerrePositivity.KST.SConstruction.relativeLeftFunctor

#check @SerrePositivity.KST.SConstruction.relativeRightFunctor
#print axioms SerrePositivity.KST.SConstruction.relativeRightFunctor

#check @SerrePositivity.KST.SConstruction.relativeCofiberPostcomp_mem
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberPostcomp_mem

#check @SerrePositivity.KST.SConstruction.relativeCofiberMap
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberMap

#check @SerrePositivity.KST.SConstruction.relativeCofiberMap_inclusion
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberMap_inclusion

#check @SerrePositivity.KST.SConstruction.relativeCofiberFunctor
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberFunctor

#check @SerrePositivity.KST.SConstruction.relativeCofiberInclusionNat
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberInclusionNat

#check @SerrePositivity.KST.SConstruction.relativeCofiberSubobject_naturality
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberSubobject_naturality

#check @SerrePositivity.KST.SConstruction.relativeCofiberSubobjectNat
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberSubobjectNat

#check @SerrePositivity.KST.SConstruction.relativeCofiberQuotient_naturality
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberQuotient_naturality

#check @SerrePositivity.KST.SConstruction.relativeCofiberQuotientNat
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberQuotientNat

#check @SerrePositivity.KST.SConstruction.relativeCofiberPair_naturality
#print axioms SerrePositivity.KST.SConstruction.relativeCofiberPair_naturality

#check @SerrePositivity.KST.SConstruction.relativeAdditivityNat
#print axioms SerrePositivity.KST.SConstruction.relativeAdditivityNat

#check @SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityNat
#print axioms SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityNat

#check @SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityLocalizedIso
#print axioms SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityLocalizedIso

#check @SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityLocalizedIso_app
#print axioms SerrePositivity.KST.SConstruction.relativeMultiRealizationAdditivityLocalizedIso_app

#check @SerrePositivity.KST.SConstruction.RelativeStableModel.ambient
#print axioms SerrePositivity.KST.SConstruction.RelativeStableModel.ambient

#check @SerrePositivity.KST.SConstruction.RelativeStableModel.left
#print axioms SerrePositivity.KST.SConstruction.RelativeStableModel.left

#check @SerrePositivity.KST.SConstruction.RelativeStableModel.right
#print axioms SerrePositivity.KST.SConstruction.RelativeStableModel.right

#check @SerrePositivity.KST.SConstruction.cutEndpoint
#print axioms SerrePositivity.KST.SConstruction.cutEndpoint

#check @SerrePositivity.KST.SConstruction.cutEndpoint_mono
#print axioms SerrePositivity.KST.SConstruction.cutEndpoint_mono

#check @SerrePositivity.KST.SConstruction.cutEndpoint_zero_zero
#print axioms SerrePositivity.KST.SConstruction.cutEndpoint_zero_zero

#check @SerrePositivity.KST.SConstruction.cutEndpoint_one_zero
#print axioms SerrePositivity.KST.SConstruction.cutEndpoint_one_zero

#check @SerrePositivity.KST.SConstruction.cutEndpoint_zero_one
#print axioms SerrePositivity.KST.SConstruction.cutEndpoint_zero_one

#check @SerrePositivity.KST.SConstruction.cutEndpoint_one_one
#print axioms SerrePositivity.KST.SConstruction.cutEndpoint_one_one

#check @SerrePositivity.KST.SConstruction.arCutSquareOrder
#print axioms SerrePositivity.KST.SConstruction.arCutSquareOrder

#check @SerrePositivity.KST.SConstruction.arCutSquareChain
#print axioms SerrePositivity.KST.SConstruction.arCutSquareChain

#check @SerrePositivity.KST.SConstruction.arCutSquareMap
#print axioms SerrePositivity.KST.SConstruction.arCutSquareMap

#check @SerrePositivity.KST.SConstruction.arCutSquareAt
#print axioms SerrePositivity.KST.SConstruction.arCutSquareAt

#check @SerrePositivity.KST.SConstruction.cutEndpoint_of_le
#print axioms SerrePositivity.KST.SConstruction.cutEndpoint_of_le

#check @SerrePositivity.KST.SConstruction.cutEndpoint_of_ge
#print axioms SerrePositivity.KST.SConstruction.cutEndpoint_of_ge

#check @SerrePositivity.KST.SConstruction.arIntervalOrder
#print axioms SerrePositivity.KST.SConstruction.arIntervalOrder

#check @SerrePositivity.KST.SConstruction.arIntervalEdge
#print axioms SerrePositivity.KST.SConstruction.arIntervalEdge

#check @SerrePositivity.KST.SConstruction.arCutSquareAt_crossing
#print axioms SerrePositivity.KST.SConstruction.arCutSquareAt_crossing

#check @SerrePositivity.KST.SConstruction.arCutSquareAt_left
#print axioms SerrePositivity.KST.SConstruction.arCutSquareAt_left

#check @SerrePositivity.KST.SConstruction.arCutSquareAt_right
#print axioms SerrePositivity.KST.SConstruction.arCutSquareAt_right

#check @SerrePositivity.KST.SConstruction.arCutSquareAt_zero_corner
#print axioms SerrePositivity.KST.SConstruction.arCutSquareAt_zero_corner

#check @SerrePositivity.KST.SConstruction.arCutSquareAt_isPushout
#print axioms SerrePositivity.KST.SConstruction.arCutSquareAt_isPushout

#check @SerrePositivity.KST.SConstruction.arCutSquareAt_isCofiber
#print axioms SerrePositivity.KST.SConstruction.arCutSquareAt_isCofiber

#check @SerrePositivity.KST.SConstruction.arCutFamily
#print axioms SerrePositivity.KST.SConstruction.arCutFamily

#check @SerrePositivity.KST.SConstruction.arCutFamily_vertex
#print axioms SerrePositivity.KST.SConstruction.arCutFamily_vertex

#check @SerrePositivity.KST.SConstruction.gappedCutCofiberFamily
#print axioms SerrePositivity.KST.SConstruction.gappedCutCofiberFamily

#check @SerrePositivity.KST.SConstruction.gappedCutCofiberFamily_ι
#print axioms SerrePositivity.KST.SConstruction.gappedCutCofiberFamily_ι

#check @SerrePositivity.KST.SConstruction.cutCornerOrder
#print axioms SerrePositivity.KST.SConstruction.cutCornerOrder

#check @SerrePositivity.KST.SConstruction.arCutSquareMap_corner
#print axioms SerrePositivity.KST.SConstruction.arCutSquareMap_corner

#check @SerrePositivity.KST.SConstruction.arCutFamily_evaluation
#print axioms SerrePositivity.KST.SConstruction.arCutFamily_evaluation

#check @SerrePositivity.KST.SConstruction.gappedCutCofiberFamily_evaluation
#print axioms SerrePositivity.KST.SConstruction.gappedCutCofiberFamily_evaluation

#check @SerrePositivity.KST.SConstruction.gappedCutCofiberFamily_isGapped
#print axioms SerrePositivity.KST.SConstruction.gappedCutCofiberFamily_isGapped

#check @SerrePositivity.KST.SConstruction.cutDiagramFamilyOperator
#print axioms SerrePositivity.KST.SConstruction.cutDiagramFamilyOperator

#check @SerrePositivity.KST.SConstruction.cutRawFamilyOperator
#print axioms SerrePositivity.KST.SConstruction.cutRawFamilyOperator

#check @SerrePositivity.KST.SConstruction.cutRawFamilyOperator_vertex
#print axioms SerrePositivity.KST.SConstruction.cutRawFamilyOperator_vertex

#check @SerrePositivity.KST.SConstruction.cutRawFamilyOperator_isCofiber
#print axioms SerrePositivity.KST.SConstruction.cutRawFamilyOperator_isCofiber

#check @SerrePositivity.KST.SConstruction.cutCofiberFamilyOperator
#print axioms SerrePositivity.KST.SConstruction.cutCofiberFamilyOperator

#check @SerrePositivity.KST.SConstruction.cutCofiberFamilyOperator_ι
#print axioms SerrePositivity.KST.SConstruction.cutCofiberFamilyOperator_ι

#check @SerrePositivity.KST.SConstruction.cutCofiberFamilyOperator_vertex_ι
#print axioms SerrePositivity.KST.SConstruction.cutCofiberFamilyOperator_vertex_ι

#check @SerrePositivity.KST.SConstruction.cutCofiberFamilyOperator_isGapped
#print axioms SerrePositivity.KST.SConstruction.cutCofiberFamilyOperator_isGapped

#check @SerrePositivity.KST.SConstruction.cutSConstructionMap
#print axioms SerrePositivity.KST.SConstruction.cutSConstructionMap

#check @SerrePositivity.KST.SConstruction.cutSConstructionMap_ι
#print axioms SerrePositivity.KST.SConstruction.cutSConstructionMap_ι

#check @SerrePositivity.KST.SConstruction.cutCofiberComparison
#print axioms SerrePositivity.KST.SConstruction.cutCofiberComparison

#check @SerrePositivity.KST.SConstruction.cutDiagramFamilyOperator_evaluation
#print axioms SerrePositivity.KST.SConstruction.cutDiagramFamilyOperator_evaluation

#check @SerrePositivity.KST.SConstruction.cutRawFamilyOperator_evaluation
#print axioms SerrePositivity.KST.SConstruction.cutRawFamilyOperator_evaluation

#check @SerrePositivity.KST.SConstruction.cutSConstructionMap_evaluation
#print axioms SerrePositivity.KST.SConstruction.cutSConstructionMap_evaluation

#check @SerrePositivity.KST.SConstruction.cutCofiberComparison_evaluation
#print axioms SerrePositivity.KST.SConstruction.cutCofiberComparison_evaluation

#check @SerrePositivity.KST.SConstruction.cutCofiberComparison_preservesCofiberData
#print axioms SerrePositivity.KST.SConstruction.cutCofiberComparison_preservesCofiberData

#check @SerrePositivity.KST.SConstruction.cutStableComparison
#print axioms SerrePositivity.KST.SConstruction.cutStableComparison

#check @SerrePositivity.KST.SConstruction.cutStableComparison_evaluation
#print axioms SerrePositivity.KST.SConstruction.cutStableComparison_evaluation

#check @SerrePositivity.KST.SConstruction.cutCornerOrder_one_zero
#print axioms SerrePositivity.KST.SConstruction.cutCornerOrder_one_zero

#check @SerrePositivity.KST.SConstruction.cutStableComparison_middle
#print axioms SerrePositivity.KST.SConstruction.cutStableComparison_middle

#check @SerrePositivity.KST.SConstruction.cutEndpoint_naturality
#print axioms SerrePositivity.KST.SConstruction.cutEndpoint_naturality

#check @SerrePositivity.KST.SConstruction.cutCornerOrder_naturality
#print axioms SerrePositivity.KST.SConstruction.cutCornerOrder_naturality

#check @SerrePositivity.KST.SConstruction.arCutSquareMap_naturality
#print axioms SerrePositivity.KST.SConstruction.arCutSquareMap_naturality

#check @SerrePositivity.KST.SConstruction.zeroStablePredicate
#print axioms SerrePositivity.KST.SConstruction.zeroStablePredicate

#check @SerrePositivity.KST.SConstruction.cutLeftSupport
#print axioms SerrePositivity.KST.SConstruction.cutLeftSupport

#check @SerrePositivity.KST.SConstruction.cutRightSupport
#print axioms SerrePositivity.KST.SConstruction.cutRightSupport

#check @SerrePositivity.KST.SConstruction.cutLeftSupport_iff
#print axioms SerrePositivity.KST.SConstruction.cutLeftSupport_iff

#check @SerrePositivity.KST.SConstruction.cutRightSupport_iff
#print axioms SerrePositivity.KST.SConstruction.cutRightSupport_iff

#check @SerrePositivity.KST.SConstruction.sConstructionVertex_diagonal_isZero
#print axioms SerrePositivity.KST.SConstruction.sConstructionVertex_diagonal_isZero

#check @SerrePositivity.KST.SConstruction.sMap_evaluate_vertex
#print axioms SerrePositivity.KST.SConstruction.sMap_evaluate_vertex

#check @SerrePositivity.KST.SConstruction.cutLeftSupport_sMap
#print axioms SerrePositivity.KST.SConstruction.cutLeftSupport_sMap

#check @SerrePositivity.KST.SConstruction.cutRightSupport_sMap
#print axioms SerrePositivity.KST.SConstruction.cutRightSupport_sMap

#check @SerrePositivity.KST.SConstruction.cutStableComparison_relative_mem
#print axioms SerrePositivity.KST.SConstruction.cutStableComparison_relative_mem

#check @SerrePositivity.KST.SConstruction.cutRelativeComparisonMap
#print axioms SerrePositivity.KST.SConstruction.cutRelativeComparisonMap

#check @SerrePositivity.KST.SConstruction.cutRelativeComparisonMap_inclusion
#print axioms SerrePositivity.KST.SConstruction.cutRelativeComparisonMap_inclusion

#check @SerrePositivity.KST.SConstruction.cutRelativeComparison
#print axioms SerrePositivity.KST.SConstruction.cutRelativeComparison

#check @SerrePositivity.KST.SConstruction.cutRelativeComparison_inclusion
#print axioms SerrePositivity.KST.SConstruction.cutRelativeComparison_inclusion

#check @SerrePositivity.KST.SConstruction.cutRelativeMiddle
#print axioms SerrePositivity.KST.SConstruction.cutRelativeMiddle

#check @SerrePositivity.KST.SConstruction.cutRelativeComparison_middle
#print axioms SerrePositivity.KST.SConstruction.cutRelativeComparison_middle

#check @SerrePositivity.KST.SConstruction.cofiberFamilyTriangle_corner
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyTriangle_corner

#check @SerrePositivity.KST.SConstruction.cofiberFamilyBottomIso
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyBottomIso

#check @SerrePositivity.KST.SConstruction.cofiberFamilyRightIso
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyRightIso

#check @SerrePositivity.KST.SConstruction.cutLeftSupport_rightCut_isZero
#print axioms SerrePositivity.KST.SConstruction.cutLeftSupport_rightCut_isZero

#check @SerrePositivity.KST.SConstruction.cutRightSupport_leftCut_isZero
#print axioms SerrePositivity.KST.SConstruction.cutRightSupport_leftCut_isZero

#check @SerrePositivity.KST.SConstruction.cutComparison_pre_evaluation
#print axioms SerrePositivity.KST.SConstruction.cutComparison_pre_evaluation

#check @SerrePositivity.KST.SConstruction.cutComparison_pre_middle
#print axioms SerrePositivity.KST.SConstruction.cutComparison_pre_middle

#check @SerrePositivity.KST.SConstruction.cutLeftSupport_normalizationIso
#print axioms SerrePositivity.KST.SConstruction.cutLeftSupport_normalizationIso

#check @SerrePositivity.KST.SConstruction.cutRightSupport_normalizationIso
#print axioms SerrePositivity.KST.SConstruction.cutRightSupport_normalizationIso

#check @SerrePositivity.KST.SConstruction.cutLeftIntervalInclusion
#print axioms SerrePositivity.KST.SConstruction.cutLeftIntervalInclusion

#check @SerrePositivity.KST.SConstruction.cutLeftIntervalRetraction
#print axioms SerrePositivity.KST.SConstruction.cutLeftIntervalRetraction

#check @SerrePositivity.KST.SConstruction.cutRightIntervalInclusion
#print axioms SerrePositivity.KST.SConstruction.cutRightIntervalInclusion

#check @SerrePositivity.KST.SConstruction.cutRightIntervalRetraction
#print axioms SerrePositivity.KST.SConstruction.cutRightIntervalRetraction

#check @SerrePositivity.KST.SConstruction.cutLeftInterval_retraction_inclusion
#print axioms SerrePositivity.KST.SConstruction.cutLeftInterval_retraction_inclusion

#check @SerrePositivity.KST.SConstruction.cutLeftInterval_inclusion_retraction
#print axioms SerrePositivity.KST.SConstruction.cutLeftInterval_inclusion_retraction

#check @SerrePositivity.KST.SConstruction.cutRightInterval_retraction_inclusion
#print axioms SerrePositivity.KST.SConstruction.cutRightInterval_retraction_inclusion

#check @SerrePositivity.KST.SConstruction.cutRightInterval_inclusion_retraction
#print axioms SerrePositivity.KST.SConstruction.cutRightInterval_inclusion_retraction

#check @SerrePositivity.KST.SConstruction.functorIsoOfFullSubcomplexPostcomp
#print axioms SerrePositivity.KST.SConstruction.functorIsoOfFullSubcomplexPostcomp

#check @SerrePositivity.KST.SConstruction.cutLeftIntervalExtension_mem
#print axioms SerrePositivity.KST.SConstruction.cutLeftIntervalExtension_mem

#check @SerrePositivity.KST.SConstruction.cutLeftIntervalExtensionMap
#print axioms SerrePositivity.KST.SConstruction.cutLeftIntervalExtensionMap

#check @SerrePositivity.KST.SConstruction.cutLeftIntervalExtensionMap_inclusion
#print axioms SerrePositivity.KST.SConstruction.cutLeftIntervalExtensionMap_inclusion

#check @SerrePositivity.KST.SConstruction.cutLeftIntervalExtension
#print axioms SerrePositivity.KST.SConstruction.cutLeftIntervalExtension

#check @SerrePositivity.KST.SConstruction.cutLeftIntervalRestriction
#print axioms SerrePositivity.KST.SConstruction.cutLeftIntervalRestriction

#check @SerrePositivity.KST.SConstruction.cutRightIntervalExtension_mem
#print axioms SerrePositivity.KST.SConstruction.cutRightIntervalExtension_mem

#check @SerrePositivity.KST.SConstruction.cutRightIntervalExtensionMap
#print axioms SerrePositivity.KST.SConstruction.cutRightIntervalExtensionMap

#check @SerrePositivity.KST.SConstruction.cutRightIntervalExtensionMap_inclusion
#print axioms SerrePositivity.KST.SConstruction.cutRightIntervalExtensionMap_inclusion

#check @SerrePositivity.KST.SConstruction.cutRightIntervalExtension
#print axioms SerrePositivity.KST.SConstruction.cutRightIntervalExtension

#check @SerrePositivity.KST.SConstruction.cutRightIntervalRestriction
#print axioms SerrePositivity.KST.SConstruction.cutRightIntervalRestriction

#check @SerrePositivity.KST.SConstruction.cutLeftInterval_extension_restriction
#print axioms SerrePositivity.KST.SConstruction.cutLeftInterval_extension_restriction

#check @SerrePositivity.KST.SConstruction.cutLeftInterval_restriction_extension_inclusion
#print axioms SerrePositivity.KST.SConstruction.cutLeftInterval_restriction_extension_inclusion

#check @SerrePositivity.KST.SConstruction.cutLeftInterval_restriction_extensionIso
#print axioms SerrePositivity.KST.SConstruction.cutLeftInterval_restriction_extensionIso

#check @SerrePositivity.KST.SConstruction.cutLeftIntervalEquivalence
#print axioms SerrePositivity.KST.SConstruction.cutLeftIntervalEquivalence

#check @SerrePositivity.KST.SConstruction.cutRightInterval_extension_restriction
#print axioms SerrePositivity.KST.SConstruction.cutRightInterval_extension_restriction

#check @SerrePositivity.KST.SConstruction.cutRightInterval_restriction_extension_inclusion
#print axioms SerrePositivity.KST.SConstruction.cutRightInterval_restriction_extension_inclusion

#check @SerrePositivity.KST.SConstruction.cutRightInterval_restriction_extensionIso
#print axioms SerrePositivity.KST.SConstruction.cutRightInterval_restriction_extensionIso

#check @SerrePositivity.KST.SConstruction.cutRightIntervalEquivalence
#print axioms SerrePositivity.KST.SConstruction.cutRightIntervalEquivalence

#check @SerrePositivity.KST.SConstruction.arrowSquareDiagonal
#print axioms SerrePositivity.KST.SConstruction.arrowSquareDiagonal

#check @SerrePositivity.KST.SConstruction.arrowTrianglePrism
#print axioms SerrePositivity.KST.SConstruction.arrowTrianglePrism

#check @SerrePositivity.KST.SConstruction.arrowTrianglePrism_zero
#print axioms SerrePositivity.KST.SConstruction.arrowTrianglePrism_zero

#check @SerrePositivity.KST.SConstruction.arrowTrianglePrism_one
#print axioms SerrePositivity.KST.SConstruction.arrowTrianglePrism_one

#check @SerrePositivity.KST.SConstruction.arrowTrianglePrism_source
#print axioms SerrePositivity.KST.SConstruction.arrowTrianglePrism_source

#check @SerrePositivity.KST.SConstruction.arrowTrianglePrism_target
#print axioms SerrePositivity.KST.SConstruction.arrowTrianglePrism_target

#check @SerrePositivity.KST.SConstruction.arrowTrianglePrismIso
#print axioms SerrePositivity.KST.SConstruction.arrowTrianglePrismIso

#check @SerrePositivity.KST.SConstruction.arrowSquareTopRightIso
#print axioms SerrePositivity.KST.SConstruction.arrowSquareTopRightIso

#check @SerrePositivity.KST.SConstruction.evaluateFunctorAt_as_ev
#print axioms SerrePositivity.KST.SConstruction.evaluateFunctorAt_as_ev

#check @SerrePositivity.KST.SConstruction.ihomUncurry_pre_row
#print axioms SerrePositivity.KST.SConstruction.ihomUncurry_pre_row

#check @SerrePositivity.KST.SConstruction.ihomUncurry_pre_column
#print axioms SerrePositivity.KST.SConstruction.ihomUncurry_pre_column

#check @SerrePositivity.KST.SConstruction.cofiberBottomEvaluationMap
#print axioms SerrePositivity.KST.SConstruction.cofiberBottomEvaluationMap

#check @SerrePositivity.KST.SConstruction.cofiberProjection_evaluation
#print axioms SerrePositivity.KST.SConstruction.cofiberProjection_evaluation

#check @SerrePositivity.KST.SConstruction.cofiberPostcomp_projection
#print axioms SerrePositivity.KST.SConstruction.cofiberPostcomp_projection

#check @SerrePositivity.KST.SConstruction.doubleCofiberGrid
#print axioms SerrePositivity.KST.SConstruction.doubleCofiberGrid

#check @SerrePositivity.KST.SConstruction.doubleCofiberRow
#print axioms SerrePositivity.KST.SConstruction.doubleCofiberRow

#check @SerrePositivity.KST.SConstruction.doubleCofiberColumn
#print axioms SerrePositivity.KST.SConstruction.doubleCofiberColumn

#check @SerrePositivity.KST.SConstruction.doubleCofiberGrid_row
#print axioms SerrePositivity.KST.SConstruction.doubleCofiberGrid_row

#check @SerrePositivity.KST.SConstruction.doubleCofiberGrid_column
#print axioms SerrePositivity.KST.SConstruction.doubleCofiberGrid_column

#check @SerrePositivity.KST.SConstruction.cofiberFamilyTriangle_input
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyTriangle_input

#check @SerrePositivity.KST.SConstruction.cofiberFamilyInput_edge_isInvertible
#print axioms SerrePositivity.KST.SConstruction.cofiberFamilyInput_edge_isInvertible

#check @SerrePositivity.KST.SConstruction.doubleCofiberGrid_bottom
#print axioms SerrePositivity.KST.SConstruction.doubleCofiberGrid_bottom

#check @SerrePositivity.KST.SConstruction.doubleCofiberGrid_left
#print axioms SerrePositivity.KST.SConstruction.doubleCofiberGrid_left

#check @SerrePositivity.KST.SConstruction.doubleCofiberGrid_top
#print axioms SerrePositivity.KST.SConstruction.doubleCofiberGrid_top

#check @SerrePositivity.KST.SConstruction.doubleCofiberGrid_right
#print axioms SerrePositivity.KST.SConstruction.doubleCofiberGrid_right

#check @SerrePositivity.KST.SConstruction.functorIsoFlip
#print axioms SerrePositivity.KST.SConstruction.functorIsoFlip

#check @SerrePositivity.KST.SConstruction.functorIsoOfFlip
#print axioms SerrePositivity.KST.SConstruction.functorIsoOfFlip

#check @SerrePositivity.KST.SConstruction.doubleCofiberInputIso
#print axioms SerrePositivity.KST.SConstruction.doubleCofiberInputIso

#check @SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily
#print axioms SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily

#check @SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_row
#print axioms SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_row

#check @SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_column
#print axioms SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_column

#check @SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_row_one
#print axioms SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_row_one

#check @SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_column_one
#print axioms SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_column_one

#check @SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_row_zero_quotient
#print axioms SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_row_zero_quotient

#check @SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_column_zero_quotient
#print axioms SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_column_zero_quotient

#check @SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_row_zero_isZero
#print axioms SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_row_zero_isZero

#check @SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_column_zero_isZero
#print axioms SerrePositivity.KST.SConstruction.cutDoubleCofiberFamily_column_zero_isZero

#check @SerrePositivity.KST.SConstruction.functorIsoOfTrivialKanFibrationPostcomp
#print axioms SerrePositivity.KST.SConstruction.functorIsoOfTrivialKanFibrationPostcomp

#check @SerrePositivity.KST.SConstruction.cutRelativeInputIso
#print axioms SerrePositivity.KST.SConstruction.cutRelativeInputIso

#check @SerrePositivity.KST.SConstruction.cutRelativeAmbientIso
#print axioms SerrePositivity.KST.SConstruction.cutRelativeAmbientIso

#check @SerrePositivity.KST.SConstruction.cutRelativeMiddle_comparisonIso
#print axioms SerrePositivity.KST.SConstruction.cutRelativeMiddle_comparisonIso

#check @SerrePositivity.KST.SConstruction.cutRelativeEquivalence
#print axioms SerrePositivity.KST.SConstruction.cutRelativeEquivalence

#check @SerrePositivity.KST.SConstruction.cutLeftSegalEvaluation
#print axioms SerrePositivity.KST.SConstruction.cutLeftSegalEvaluation

#check @SerrePositivity.KST.SConstruction.cutRightSegalEvaluation
#print axioms SerrePositivity.KST.SConstruction.cutRightSegalEvaluation

#check @SerrePositivity.KST.SConstruction.cutRelativeComparison_leftSegal
#print axioms SerrePositivity.KST.SConstruction.cutRelativeComparison_leftSegal

#check @SerrePositivity.KST.SConstruction.cutRelativeComparison_rightSegal
#print axioms SerrePositivity.KST.SConstruction.cutRelativeComparison_rightSegal

#check @SerrePositivity.KST.SConstruction.cutRelativeSegalPair
#print axioms SerrePositivity.KST.SConstruction.cutRelativeSegalPair

#check @SerrePositivity.KST.SConstruction.sPostcompositionFunctorIso
#print axioms SerrePositivity.KST.SConstruction.sPostcompositionFunctorIso

#check @SerrePositivity.KST.SConstruction.StableModelEquivalence
#print axioms SerrePositivity.KST.SConstruction.StableModelEquivalence

#check @SerrePositivity.KST.SConstruction.StableModelEquivalence.toQCatEquivalence
#print axioms SerrePositivity.KST.SConstruction.StableModelEquivalence.toQCatEquivalence

#check @SerrePositivity.KST.SConstruction.StableModelEquivalence.symm
#print axioms SerrePositivity.KST.SConstruction.StableModelEquivalence.symm

#check @SerrePositivity.KST.SConstruction.StableModelEquivalence.sConstruction
#print axioms SerrePositivity.KST.SConstruction.StableModelEquivalence.sConstruction

#check @SerrePositivity.KST.SConstruction.StableModelEquivalence.hom
#print axioms SerrePositivity.KST.SConstruction.StableModelEquivalence.hom

#check @SerrePositivity.KST.SConstruction.StableModelEquivalence.inv
#print axioms SerrePositivity.KST.SConstruction.StableModelEquivalence.inv

#check @SerrePositivity.KST.SConstruction.StableModelEquivalence.homInvIso
#print axioms SerrePositivity.KST.SConstruction.StableModelEquivalence.homInvIso

#check @SerrePositivity.KST.SConstruction.StableModelEquivalence.invHomIso
#print axioms SerrePositivity.KST.SConstruction.StableModelEquivalence.invHomIso

#check @SerrePositivity.KST.SConstruction.objectS_map_localized_isIso_of_equivalence
#print axioms SerrePositivity.KST.SConstruction.objectS_map_localized_isIso_of_equivalence

#check @SerrePositivity.KST.SConstruction.coreSRealization_map_localized_isIso_of_equivalence
#print axioms SerrePositivity.KST.SConstruction.coreSRealization_map_localized_isIso_of_equivalence

#check @SerrePositivity.KST.SConstruction.multiRealization_map_one_localized_isIso_of_equivalence
#print axioms SerrePositivity.KST.SConstruction.multiRealization_map_one_localized_isIso_of_equivalence

#check @SerrePositivity.KST.SConstruction.multiRealization_map_step_localized_isIso_of_equivalence
#print axioms SerrePositivity.KST.SConstruction.multiRealization_map_step_localized_isIso_of_equivalence

#check @SerrePositivity.KST.SConstruction.multiRealization_map_localized_isIso_of_equivalence
#print axioms SerrePositivity.KST.SConstruction.multiRealization_map_localized_isIso_of_equivalence

#check @SerrePositivity.KST.SConstruction.cutRelativeStableEquivalence
#print axioms SerrePositivity.KST.SConstruction.cutRelativeStableEquivalence

#check @SerrePositivity.KST.SConstruction.cutLeftIntervalStableEquivalence
#print axioms SerrePositivity.KST.SConstruction.cutLeftIntervalStableEquivalence

#check @SerrePositivity.KST.SConstruction.cutRightIntervalStableEquivalence
#print axioms SerrePositivity.KST.SConstruction.cutRightIntervalStableEquivalence

#check @SerrePositivity.KST.SConstruction.cutIntervalRestrictions_tensor_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.cutIntervalRestrictions_tensor_localized_isIso

#check @SerrePositivity.KST.SConstruction.cutSegalMap
#print axioms SerrePositivity.KST.SConstruction.cutSegalMap

#check @SerrePositivity.KST.SConstruction.cutSegalMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.cutSegalMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.cutSegalPair_naturality
#print axioms SerrePositivity.KST.SConstruction.cutSegalPair_naturality

#check @SerrePositivity.KST.SConstruction.cutSegalNat
#print axioms SerrePositivity.KST.SConstruction.cutSegalNat

#check @SerrePositivity.KST.SConstruction.cutSegalLocalizedIso
#print axioms SerrePositivity.KST.SConstruction.cutSegalLocalizedIso

#check @SerrePositivity.KST.SConstruction.cutSegalLocalizedIso_app
#print axioms SerrePositivity.KST.SConstruction.cutSegalLocalizedIso_app

#check @SerrePositivity.KST.SConstruction.edgeIntervalInclusion
#print axioms SerrePositivity.KST.SConstruction.edgeIntervalInclusion

#check @SerrePositivity.KST.SConstruction.edgeSegalEvaluation
#print axioms SerrePositivity.KST.SConstruction.edgeSegalEvaluation

#check @SerrePositivity.KST.SConstruction.edgeSegalEvaluation_one
#print axioms SerrePositivity.KST.SConstruction.edgeSegalEvaluation_one

#check @SerrePositivity.KST.SConstruction.cutLeftSegalEvaluation_first
#print axioms SerrePositivity.KST.SConstruction.cutLeftSegalEvaluation_first

#check @SerrePositivity.KST.SConstruction.cutRightSegalEvaluation_edge
#print axioms SerrePositivity.KST.SConstruction.cutRightSegalEvaluation_edge

#check @SerrePositivity.KST.SConstruction.nonemptySSetPower
#print axioms SerrePositivity.KST.SConstruction.nonemptySSetPower

#check @SerrePositivity.KST.SConstruction.nonemptySSetPowerProjection
#print axioms SerrePositivity.KST.SConstruction.nonemptySSetPowerProjection

#check @SerrePositivity.KST.SConstruction.nonemptySSetPowerLift
#print axioms SerrePositivity.KST.SConstruction.nonemptySSetPowerLift

#check @SerrePositivity.KST.SConstruction.nonemptySSetPowerLift_projection
#print axioms SerrePositivity.KST.SConstruction.nonemptySSetPowerLift_projection

#check @SerrePositivity.KST.SConstruction.nonemptySSetPowerLift_comp
#print axioms SerrePositivity.KST.SConstruction.nonemptySSetPowerLift_comp

#check @SerrePositivity.KST.SConstruction.edgeSegalMap
#print axioms SerrePositivity.KST.SConstruction.edgeSegalMap

#check @SerrePositivity.KST.SConstruction.edgeSegalMap_projection
#print axioms SerrePositivity.KST.SConstruction.edgeSegalMap_projection

#check @SerrePositivity.KST.SConstruction.edgeSegalMap_zero
#print axioms SerrePositivity.KST.SConstruction.edgeSegalMap_zero

#check @SerrePositivity.KST.SConstruction.edgeSegalMap_succ
#print axioms SerrePositivity.KST.SConstruction.edgeSegalMap_succ

#check @SerrePositivity.KST.SConstruction.edgeSegalMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.edgeSegalMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.pathFirstEdge_naturality
#print axioms SerrePositivity.KST.SConstruction.pathFirstEdge_naturality

#check @SerrePositivity.KST.SConstruction.pathHeadSegalMap
#print axioms SerrePositivity.KST.SConstruction.pathHeadSegalMap

#check @SerrePositivity.KST.SConstruction.pathHeadSegalMap_fst
#print axioms SerrePositivity.KST.SConstruction.pathHeadSegalMap_fst

#check @SerrePositivity.KST.SConstruction.pathHeadSegalMap_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.pathHeadSegalMap_localized_isIso

#check @SerrePositivity.KST.SConstruction.pathHeadSegalMap_naturality
#print axioms SerrePositivity.KST.SConstruction.pathHeadSegalMap_naturality

#check @SerrePositivity.KST.SConstruction.iteratedPathBoundary_headPreserving_homotopyPullback
#print axioms SerrePositivity.KST.SConstruction.iteratedPathBoundary_headPreserving_homotopyPullback

#check @SerrePositivity.KST.SConstruction.trivialKanFibration_of_simplexSurjective_baseChange
#print axioms SerrePositivity.KST.SConstruction.trivialKanFibration_of_simplexSurjective_baseChange

#check @SerrePositivity.KST.SConstruction.fibration_vertex_surjective_of_connected
#print axioms SerrePositivity.KST.SConstruction.fibration_vertex_surjective_of_connected

#check @SerrePositivity.KST.SConstruction.fibration_simplex_surjective_of_vertex_surjective
#print axioms SerrePositivity.KST.SConstruction.fibration_simplex_surjective_of_vertex_surjective

#check @SerrePositivity.KST.SConstruction.fibration_simplex_surjective_of_connected
#print axioms SerrePositivity.KST.SConstruction.fibration_simplex_surjective_of_connected

#check @SerrePositivity.KST.SConstruction.localized_isIso_of_simplexSurjective_fibration_baseChange
#print axioms SerrePositivity.KST.SConstruction.localized_isIso_of_simplexSurjective_fibration_baseChange

#check @SerrePositivity.KST.SConstruction.localized_isIso_of_connected_fibration_baseChange
#print axioms SerrePositivity.KST.SConstruction.localized_isIso_of_connected_fibration_baseChange

#check @SerrePositivity.KST.SConstruction.pullbackMapBase_slice_naturality
#print axioms SerrePositivity.KST.SConstruction.pullbackMapBase_slice_naturality

#check @SerrePositivity.KST.SConstruction.localized_isIso_of_connected_baseChange
#print axioms SerrePositivity.KST.SConstruction.localized_isIso_of_connected_baseChange

#check @SerrePositivity.KST.SConstruction.splitBasePullback_projection
#print axioms SerrePositivity.KST.SConstruction.splitBasePullback_projection

#check @SerrePositivity.KST.SConstruction.splitBasePullbackIso
#print axioms SerrePositivity.KST.SConstruction.splitBasePullbackIso

#check @SerrePositivity.KST.SConstruction.homotopyPullback_retraction_of_section
#print axioms SerrePositivity.KST.SConstruction.homotopyPullback_retraction_of_section

#check @SerrePositivity.KST.SConstruction.naturality_homotopyPullback_retraction_of_section_of_kan
#print axioms SerrePositivity.KST.SConstruction.naturality_homotopyPullback_retraction_of_section_of_kan

#check @SerrePositivity.KST.SConstruction.naturality_homotopyPullback_retraction_of_section
#print axioms SerrePositivity.KST.SConstruction.naturality_homotopyPullback_retraction_of_section

#check @SerrePositivity.KST.SConstruction.iteratedSRealizationDiagram_positive_isConnected
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealizationDiagram_positive_isConnected

#check @SerrePositivity.KST.SConstruction.iteratedPathBoundary_firstFace_homotopyPullback
#print axioms SerrePositivity.KST.SConstruction.iteratedPathBoundary_firstFace_homotopyPullback

#check @SerrePositivity.KST.SConstruction.naturality_homotopyPullback_id
#print axioms SerrePositivity.KST.SConstruction.naturality_homotopyPullback_id

#check @SerrePositivity.KST.SConstruction.naturality_homotopyPullback_comp
#print axioms SerrePositivity.KST.SConstruction.naturality_homotopyPullback_comp

#check @SerrePositivity.KST.SConstruction.simplicial_naturality_homotopyPullback_of_generators
#print axioms SerrePositivity.KST.SConstruction.simplicial_naturality_homotopyPullback_of_generators

#check @SerrePositivity.KST.SConstruction.iteratedPathBoundary_face_homotopyPullback
#print axioms SerrePositivity.KST.SConstruction.iteratedPathBoundary_face_homotopyPullback

#check @SerrePositivity.KST.SConstruction.iteratedPathBoundary_degeneracy_homotopyPullback
#print axioms SerrePositivity.KST.SConstruction.iteratedPathBoundary_degeneracy_homotopyPullback

#check @SerrePositivity.KST.SConstruction.iteratedPathBoundary_homotopyPullback
#print axioms SerrePositivity.KST.SConstruction.iteratedPathBoundary_homotopyPullback

#check @SerrePositivity.KST.SConstruction.iteratedPathBoundary_realization_homotopyPullback
#print axioms SerrePositivity.KST.SConstruction.iteratedPathBoundary_realization_homotopyPullback

#check @SerrePositivity.KST.SConstruction.diagonalZeroColumn_eq_rowEvaluation
#print axioms SerrePositivity.KST.SConstruction.diagonalZeroColumn_eq_rowEvaluation

#check @SerrePositivity.KST.SConstruction.diagonalZeroColumn_homotopyPullback_of_zeroRow
#print axioms SerrePositivity.KST.SConstruction.diagonalZeroColumn_homotopyPullback_of_zeroRow

#check @SerrePositivity.KST.SConstruction.iteratedPathBoundary_zeroRow_homotopyPullback
#print axioms SerrePositivity.KST.SConstruction.iteratedPathBoundary_zeroRow_homotopyPullback

#check @SerrePositivity.KST.SConstruction.iteratedPathToKan
#print axioms SerrePositivity.KST.SConstruction.iteratedPathToKan

#check @SerrePositivity.KST.SConstruction.iteratedRealizationToKan
#print axioms SerrePositivity.KST.SConstruction.iteratedRealizationToKan

#check @SerrePositivity.KST.SConstruction.iteratedPathToKan_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.iteratedPathToKan_localized_isIso

#check @SerrePositivity.KST.SConstruction.iteratedRealizationToKan_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.iteratedRealizationToKan_localized_isIso

#check @SerrePositivity.KST.SConstruction.iteratedBoundaryToKan_comm
#print axioms SerrePositivity.KST.SConstruction.iteratedBoundaryToKan_comm

#check @SerrePositivity.KST.SConstruction.iteratedRealizationToKan_zeroColumn
#print axioms SerrePositivity.KST.SConstruction.iteratedRealizationToKan_zeroColumn

#check @SerrePositivity.KST.SConstruction.zeroRowPathToKan
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathToKan

#check @SerrePositivity.KST.SConstruction.zeroRowPathToKan_boundary
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathToKan_boundary

#check @SerrePositivity.KST.SConstruction.zeroRowKanBoundary_homotopyPullback
#print axioms SerrePositivity.KST.SConstruction.zeroRowKanBoundary_homotopyPullback

#check @SerrePositivity.KST.SConstruction.basedPathBasepoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.basedPathBasepoint_localized_isIso

#check @SerrePositivity.KST.SConstruction.strictZeroPathFiberMap
#print axioms SerrePositivity.KST.SConstruction.strictZeroPathFiberMap

#check @SerrePositivity.KST.SConstruction.strictZeroPathFiberMap_path
#print axioms SerrePositivity.KST.SConstruction.strictZeroPathFiberMap_path

#check @SerrePositivity.KST.SConstruction.strictZeroPathFiberMap_projection
#print axioms SerrePositivity.KST.SConstruction.strictZeroPathFiberMap_projection

#check @SerrePositivity.KST.SConstruction.strictZeroPathFiberMap_localized_isIso_of_homotopyPullback
#print axioms SerrePositivity.KST.SConstruction.strictZeroPathFiberMap_localized_isIso_of_homotopyPullback

#check @SerrePositivity.KST.SConstruction.zeroRowPathFiberComparison
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathFiberComparison

#check @SerrePositivity.KST.SConstruction.zeroRowPathFiberComparison_projection
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathFiberComparison_projection

#check @SerrePositivity.KST.SConstruction.zeroRowPathFiberComparison_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathFiberComparison_localized_isIso

#check @SerrePositivity.KST.SConstruction.simplicialPathZeroColumn_section
#print axioms SerrePositivity.KST.SConstruction.simplicialPathZeroColumn_section

#check @SerrePositivity.KST.SConstruction.zeroRowPathToKan_degeneracy
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathToKan_degeneracy

#check @SerrePositivity.KST.SConstruction.zeroRowPathFiberComparison_degeneracy
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathFiberComparison_degeneracy

#check @SerrePositivity.KST.SConstruction.zeroRowPointedModel
#print axioms SerrePositivity.KST.SConstruction.zeroRowPointedModel

#check @SerrePositivity.KST.SConstruction.zeroRowPointedFiberComparison
#print axioms SerrePositivity.KST.SConstruction.zeroRowPointedFiberComparison

#check @SerrePositivity.KST.SConstruction.zeroRowPointedFiberComparison_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroRowPointedFiberComparison_localized_isIso

#check @SerrePositivity.KST.SConstruction.exists_pointedKanStrictExtension
#print axioms SerrePositivity.KST.SConstruction.exists_pointedKanStrictExtension

#check @SerrePositivity.KST.SConstruction.pointedKanStrictExtension
#print axioms SerrePositivity.KST.SConstruction.pointedKanStrictExtension

#check @SerrePositivity.KST.SConstruction.pointedKanStrictExtension_fac
#print axioms SerrePositivity.KST.SConstruction.pointedKanStrictExtension_fac

#check @SerrePositivity.KST.SConstruction.pointedKanStrictExtension_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.pointedKanStrictExtension_piIsomorphism

#check @SerrePositivity.KST.SConstruction.zeroRowKanFiberComparison
#print axioms SerrePositivity.KST.SConstruction.zeroRowKanFiberComparison

#check @SerrePositivity.KST.SConstruction.zeroRowKanFiberComparison_fac
#print axioms SerrePositivity.KST.SConstruction.zeroRowKanFiberComparison_fac

#check @SerrePositivity.KST.SConstruction.zeroRowKanFiberComparison_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.zeroRowKanFiberComparison_piIsomorphism

#check @SerrePositivity.KST.SConstruction.zeroRowPreviousComparison
#print axioms SerrePositivity.KST.SConstruction.zeroRowPreviousComparison

#check @SerrePositivity.KST.SConstruction.zeroRowPreviousComparison_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroRowPreviousComparison_localized_isIso

#check @SerrePositivity.KST.SConstruction.zeroRowPointedPreviousComparison
#print axioms SerrePositivity.KST.SConstruction.zeroRowPointedPreviousComparison

#check @SerrePositivity.KST.SConstruction.zeroRowPointedPreviousComparison_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroRowPointedPreviousComparison_localized_isIso

#check @SerrePositivity.KST.SConstruction.zeroRowKanPreviousComparison
#print axioms SerrePositivity.KST.SConstruction.zeroRowKanPreviousComparison

#check @SerrePositivity.KST.SConstruction.zeroRowKanPreviousComparison_piIsomorphism
#print axioms SerrePositivity.KST.SConstruction.zeroRowKanPreviousComparison_piIsomorphism

#check @SerrePositivity.KST.SConstruction.exists_previousStage_pathFiber_comparison
#print axioms SerrePositivity.KST.SConstruction.exists_previousStage_pathFiber_comparison

#check @SerrePositivity.KST.SConstruction.simplicialFixedSInterchangeNatIso
#print axioms SerrePositivity.KST.SConstruction.simplicialFixedSInterchangeNatIso

#check @SerrePositivity.KST.SConstruction.diagonalFixedSInterchangeNatIso
#print axioms SerrePositivity.KST.SConstruction.diagonalFixedSInterchangeNatIso

#check @SerrePositivity.KST.SConstruction.diagonalFixedSInterchangeNatIso_zero_app
#print axioms SerrePositivity.KST.SConstruction.diagonalFixedSInterchangeNatIso_zero_app

#check @SerrePositivity.KST.SConstruction.diagonalFixedSInterchangeNatIso_succ_app
#print axioms SerrePositivity.KST.SConstruction.diagonalFixedSInterchangeNatIso_succ_app

#check @SerrePositivity.KST.SConstruction.sInterchangeStableIso_sOneComparison_right
#print axioms SerrePositivity.KST.SConstruction.sInterchangeStableIso_sOneComparison_right

#check @SerrePositivity.KST.SConstruction.diagonalFixedSInterchangeNatIso_sOneComparison
#print axioms SerrePositivity.KST.SConstruction.diagonalFixedSInterchangeNatIso_sOneComparison

#check @SerrePositivity.KST.SConstruction.fixedSInnerCoreDiagram
#print axioms SerrePositivity.KST.SConstruction.fixedSInnerCoreDiagram

#check @SerrePositivity.KST.SConstruction.fixedSOuterCoreDiagram
#print axioms SerrePositivity.KST.SConstruction.fixedSOuterCoreDiagram

#check @SerrePositivity.KST.SConstruction.fixedSCoreDiagramSwapIso
#print axioms SerrePositivity.KST.SConstruction.fixedSCoreDiagramSwapIso

#check @SerrePositivity.KST.SConstruction.fixedSInnerCoreDiagramIso
#print axioms SerrePositivity.KST.SConstruction.fixedSInnerCoreDiagramIso

#check @SerrePositivity.KST.SConstruction.fixedSInnerRealizationIso
#print axioms SerrePositivity.KST.SConstruction.fixedSInnerRealizationIso

#check @SerrePositivity.KST.SConstruction.fixedSOneOuterCoreDiagramIso
#print axioms SerrePositivity.KST.SConstruction.fixedSOneOuterCoreDiagramIso

#check @SerrePositivity.KST.SConstruction.sOneInnerOuterRealizationIso
#print axioms SerrePositivity.KST.SConstruction.sOneInnerOuterRealizationIso

#check @SerrePositivity.KST.SConstruction.sDoubleInclusion
#print axioms SerrePositivity.KST.SConstruction.sDoubleInclusion

#check @SerrePositivity.KST.SConstruction.sDoubleInclusion_mono
#print axioms SerrePositivity.KST.SConstruction.sDoubleInclusion_mono

#check @SerrePositivity.KST.SConstruction.sInterchange_doubleInclusion
#print axioms SerrePositivity.KST.SConstruction.sInterchange_doubleInclusion

#check @SerrePositivity.KST.SConstruction.sDoubleInclusion_postcomp
#print axioms SerrePositivity.KST.SConstruction.sDoubleInclusion_postcomp

#check @SerrePositivity.KST.SConstruction.sDoubleInclusion_outerMap
#print axioms SerrePositivity.KST.SConstruction.sDoubleInclusion_outerMap

#check @SerrePositivity.KST.SConstruction.sDoubleInclusion_innerMap
#print axioms SerrePositivity.KST.SConstruction.sDoubleInclusion_innerMap

#check @SerrePositivity.KST.SConstruction.sInterchangeTransposeDiagram_vertex_ι
#print axioms SerrePositivity.KST.SConstruction.sInterchangeTransposeDiagram_vertex_ι

#check @SerrePositivity.KST.SConstruction.sInterchangeTransposeDiagram_isGapped
#print axioms SerrePositivity.KST.SConstruction.sInterchangeTransposeDiagram_isGapped

#check @SerrePositivity.KST.SConstruction.sInterchange
#print axioms SerrePositivity.KST.SConstruction.sInterchange

#check @SerrePositivity.KST.SConstruction.sInterchange_ι
#print axioms SerrePositivity.KST.SConstruction.sInterchange_ι

#check @SerrePositivity.KST.SConstruction.sInterchange_double_ι
#print axioms SerrePositivity.KST.SConstruction.sInterchange_double_ι

#check @SerrePositivity.KST.SConstruction.sInterchangeStableIso_evaluate_left
#print axioms SerrePositivity.KST.SConstruction.sInterchangeStableIso_evaluate_left

#check @SerrePositivity.KST.SConstruction.sInterchangeStableIso_evaluate_right
#print axioms SerrePositivity.KST.SConstruction.sInterchangeStableIso_evaluate_right

#check @SerrePositivity.KST.SConstruction.sOneComparison_eq_evaluation
#print axioms SerrePositivity.KST.SConstruction.sOneComparison_eq_evaluation

#check @SerrePositivity.KST.SConstruction.sInterchangeStableIso_sOneComparison
#print axioms SerrePositivity.KST.SConstruction.sInterchangeStableIso_sOneComparison

#check @SerrePositivity.KST.SConstruction.sInterchange_twice
#print axioms SerrePositivity.KST.SConstruction.sInterchange_twice

#check @SerrePositivity.KST.SConstruction.sInterchangeIso
#print axioms SerrePositivity.KST.SConstruction.sInterchangeIso

#check @SerrePositivity.KST.SConstruction.sInterchangeStableIso_naturality
#print axioms SerrePositivity.KST.SConstruction.sInterchangeStableIso_naturality

#check @SerrePositivity.KST.SConstruction.sInterchangeEndofunctorIso
#print axioms SerrePositivity.KST.SConstruction.sInterchangeEndofunctorIso

#check @SerrePositivity.KST.SConstruction.sInterchange_outerMap
#print axioms SerrePositivity.KST.SConstruction.sInterchange_outerMap

#check @SerrePositivity.KST.SConstruction.sInterchange_innerMap
#print axioms SerrePositivity.KST.SConstruction.sInterchange_innerMap

#check @SerrePositivity.KST.SConstruction.sInterchangeStableIso
#print axioms SerrePositivity.KST.SConstruction.sInterchangeStableIso

#check @SerrePositivity.KST.SConstruction.sInterchangeRawTranspose
#print axioms SerrePositivity.KST.SConstruction.sInterchangeRawTranspose

#check @SerrePositivity.KST.SConstruction.sInterchangeRawTranspose_vertex
#print axioms SerrePositivity.KST.SConstruction.sInterchangeRawTranspose_vertex

#check @SerrePositivity.KST.SConstruction.sInterchangeRawTranspose_gapped
#print axioms SerrePositivity.KST.SConstruction.sInterchangeRawTranspose_gapped

#check @SerrePositivity.KST.SConstruction.sInterchangeTransposeDiagram
#print axioms SerrePositivity.KST.SConstruction.sInterchangeTransposeDiagram

#check @SerrePositivity.KST.SConstruction.sInterchangeTransposeDiagram_ι
#print axioms SerrePositivity.KST.SConstruction.sInterchangeTransposeDiagram_ι

#check @SerrePositivity.KST.SConstruction.sOneInnerOuterRealizationIso_comparison
#print axioms SerrePositivity.KST.SConstruction.sOneInnerOuterRealizationIso_comparison

#check @SerrePositivity.KST.SConstruction.internalHomSwap_postcomp
#print axioms SerrePositivity.KST.SConstruction.internalHomSwap_postcomp

#check @SerrePositivity.KST.SConstruction.internalHomSwap_pre_left
#print axioms SerrePositivity.KST.SConstruction.internalHomSwap_pre_left

#check @SerrePositivity.KST.SConstruction.diagonalSCyclicInterchangeNatIso
#print axioms SerrePositivity.KST.SConstruction.diagonalSCyclicInterchangeNatIso

#check @SerrePositivity.KST.SConstruction.diagonalSCyclicCoreIso
#print axioms SerrePositivity.KST.SConstruction.diagonalSCyclicCoreIso

#check @SerrePositivity.KST.SConstruction.diagonalOuterSCoreDiagramIso
#print axioms SerrePositivity.KST.SConstruction.diagonalOuterSCoreDiagramIso

#check @SerrePositivity.KST.SConstruction.iteratedSRealizationCyclicIso
#print axioms SerrePositivity.KST.SConstruction.iteratedSRealizationCyclicIso

#check @SerrePositivity.KST.SConstruction.diagonalFixedSInterchangeNatIso_index
#print axioms SerrePositivity.KST.SConstruction.diagonalFixedSInterchangeNatIso_index

#check @SerrePositivity.KST.SConstruction.sOneInnerOuterRealizationIso_assembly
#print axioms SerrePositivity.KST.SConstruction.sOneInnerOuterRealizationIso_assembly

#check @SerrePositivity.KST.SConstruction.coordinateZeroInclusion_naturality
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroInclusion_naturality

#check @SerrePositivity.KST.SConstruction.coordinateZeroRange_image_iso
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroRange_image_iso

#check @SerrePositivity.KST.SConstruction.coordinateZeroBoundary_image_iso
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroBoundary_image_iso

#check @SerrePositivity.KST.SConstruction.multiFixedSEndofunctorIso
#print axioms SerrePositivity.KST.SConstruction.multiFixedSEndofunctorIso

#check @SerrePositivity.KST.SConstruction.multiFixedSEndofunctorIso_zero_app
#print axioms SerrePositivity.KST.SConstruction.multiFixedSEndofunctorIso_zero_app

#check @SerrePositivity.KST.SConstruction.multiFixedSEndofunctorIso_succ_app
#print axioms SerrePositivity.KST.SConstruction.multiFixedSEndofunctorIso_succ_app

#check @SerrePositivity.KST.SConstruction.multiFixedSEndofunctorIso_diagonal_app
#print axioms SerrePositivity.KST.SConstruction.multiFixedSEndofunctorIso_diagonal_app

#check @SerrePositivity.KST.SConstruction.multiFixedSEndofunctorIso_naturality
#print axioms SerrePositivity.KST.SConstruction.multiFixedSEndofunctorIso_naturality

#check @SerrePositivity.KST.SConstruction.multiCoreSOne_map
#print axioms SerrePositivity.KST.SConstruction.multiCoreSOne_map

#check @SerrePositivity.KST.SConstruction.multiSOneSlideCoreAt
#print axioms SerrePositivity.KST.SConstruction.multiSOneSlideCoreAt

#check @SerrePositivity.KST.SConstruction.multiSOneSlideCoreAt_hom
#print axioms SerrePositivity.KST.SConstruction.multiSOneSlideCoreAt_hom

#check @SerrePositivity.KST.SConstruction.multiSOneSlideCoreAt_naturality
#print axioms SerrePositivity.KST.SConstruction.multiSOneSlideCoreAt_naturality

#check @SerrePositivity.KST.SConstruction.multiSOneSlideCoreIso
#print axioms SerrePositivity.KST.SConstruction.multiSOneSlideCoreIso

#check @SerrePositivity.KST.SConstruction.multiSOneSlideCoreIso_realization
#print axioms SerrePositivity.KST.SConstruction.multiSOneSlideCoreIso_realization

#check @SerrePositivity.KST.SConstruction.sOneInnerOuterRealizationIso_fatBoundary
#print axioms SerrePositivity.KST.SConstruction.sOneInnerOuterRealizationIso_fatBoundary

#check @SerrePositivity.KST.SConstruction.sOneInnerOuterReducedIso
#print axioms SerrePositivity.KST.SConstruction.sOneInnerOuterReducedIso

#check @SerrePositivity.KST.SConstruction.sOneInnerOuterReducedIso_quotient
#print axioms SerrePositivity.KST.SConstruction.sOneInnerOuterReducedIso_quotient

#check @SerrePositivity.KST.SConstruction.sOneInnerOuterReducedIso_comparison
#print axioms SerrePositivity.KST.SConstruction.sOneInnerOuterReducedIso_comparison

#check @SerrePositivity.KST.SConstruction.subcomplexCofiberMap
#print axioms SerrePositivity.KST.SConstruction.subcomplexCofiberMap

#check @SerrePositivity.KST.SConstruction.subcomplexCofiberMap_quotient
#print axioms SerrePositivity.KST.SConstruction.subcomplexCofiberMap_quotient

#check @SerrePositivity.KST.SConstruction.subcomplex_image_iso_inv
#print axioms SerrePositivity.KST.SConstruction.subcomplex_image_iso_inv

#check @SerrePositivity.KST.SConstruction.subcomplexCofiberIso
#print axioms SerrePositivity.KST.SConstruction.subcomplexCofiberIso

#check @SerrePositivity.KST.SConstruction.coordinatePermutationDiagonalIso
#print axioms SerrePositivity.KST.SConstruction.coordinatePermutationDiagonalIso

#check @SerrePositivity.KST.SConstruction.zeroDirectionsIndexEndomorphism_permutation
#print axioms SerrePositivity.KST.SConstruction.zeroDirectionsIndexEndomorphism_permutation

#check @SerrePositivity.KST.SConstruction.coordinateZeroRange_permutation
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroRange_permutation

#check @SerrePositivity.KST.SConstruction.coordinateZeroBoundary_permutation
#print axioms SerrePositivity.KST.SConstruction.coordinateZeroBoundary_permutation

#check @SerrePositivity.KST.SConstruction.innerVariableOuterMap
#print axioms SerrePositivity.KST.SConstruction.innerVariableOuterMap

#check @SerrePositivity.KST.SConstruction.innerVariableOuterMap_succ
#print axioms SerrePositivity.KST.SConstruction.innerVariableOuterMap_succ

#check @SerrePositivity.KST.SConstruction.innerVariableSComparisonIso_outer_naturality
#print axioms SerrePositivity.KST.SConstruction.innerVariableSComparisonIso_outer_naturality

#check @SerrePositivity.KST.SConstruction.multiFixedSEndofunctorIso_index
#print axioms SerrePositivity.KST.SConstruction.multiFixedSEndofunctorIso_index

#check @SerrePositivity.KST.SConstruction.multiMovingSCoreIso_fatBoundary
#print axioms SerrePositivity.KST.SConstruction.multiMovingSCoreIso_fatBoundary

#check @SerrePositivity.KST.SConstruction.multiMovingSBoundaryIso
#print axioms SerrePositivity.KST.SConstruction.multiMovingSBoundaryIso

#check @SerrePositivity.KST.SConstruction.multiMovingSBoundaryIso_quotient
#print axioms SerrePositivity.KST.SConstruction.multiMovingSBoundaryIso_quotient

#check @SerrePositivity.KST.SConstruction.multiInnerSCoreConstruction
#print axioms SerrePositivity.KST.SConstruction.multiInnerSCoreConstruction

#check @SerrePositivity.KST.SConstruction.multiOuterSCoreIso
#print axioms SerrePositivity.KST.SConstruction.multiOuterSCoreIso

#check @SerrePositivity.KST.SConstruction.multiMovingSCoreIso
#print axioms SerrePositivity.KST.SConstruction.multiMovingSCoreIso

#check @SerrePositivity.KST.SConstruction.multiInnerSCoreDiagonalIso
#print axioms SerrePositivity.KST.SConstruction.multiInnerSCoreDiagonalIso

#check @SerrePositivity.KST.SConstruction.iteratedSMultiInnerRealizationIso
#print axioms SerrePositivity.KST.SConstruction.iteratedSMultiInnerRealizationIso

#check @SerrePositivity.KST.SConstruction.multiMovingSCoreIso_realization
#print axioms SerrePositivity.KST.SConstruction.multiMovingSCoreIso_realization

#check @SerrePositivity.KST.SConstruction.multiHeadSEndofunctor
#print axioms SerrePositivity.KST.SConstruction.multiHeadSEndofunctor

#check @SerrePositivity.KST.SConstruction.multiTailSEndofunctor
#print axioms SerrePositivity.KST.SConstruction.multiTailSEndofunctor

#check @SerrePositivity.KST.SConstruction.multiInnerSEndofunctor
#print axioms SerrePositivity.KST.SConstruction.multiInnerSEndofunctor

#check @SerrePositivity.KST.SConstruction.multiMovingSInterchangeNatIso
#print axioms SerrePositivity.KST.SConstruction.multiMovingSInterchangeNatIso

#check @SerrePositivity.KST.SConstruction.multiInnerSCoordinateRealizationIso_fatBoundary
#print axioms SerrePositivity.KST.SConstruction.multiInnerSCoordinateRealizationIso_fatBoundary

#check @SerrePositivity.KST.SConstruction.cyclicRealizationIso
#print axioms SerrePositivity.KST.SConstruction.cyclicRealizationIso

#check @SerrePositivity.KST.SConstruction.cyclicRealizationIso_hom
#print axioms SerrePositivity.KST.SConstruction.cyclicRealizationIso_hom

#check @SerrePositivity.KST.SConstruction.cyclicRealizationIso_fatBoundary
#print axioms SerrePositivity.KST.SConstruction.cyclicRealizationIso_fatBoundary

#check @SerrePositivity.KST.SConstruction.cyclicBoundaryIso
#print axioms SerrePositivity.KST.SConstruction.cyclicBoundaryIso

#check @SerrePositivity.KST.SConstruction.cyclicBoundaryIso_quotient
#print axioms SerrePositivity.KST.SConstruction.cyclicBoundaryIso_quotient

#check @SerrePositivity.KST.SConstruction.cyclicBoundaryIso_coordinate_quotient
#print axioms SerrePositivity.KST.SConstruction.cyclicBoundaryIso_coordinate_quotient

#check @SerrePositivity.KST.SConstruction.innerVariableOuterMap_last
#print axioms SerrePositivity.KST.SConstruction.innerVariableOuterMap_last

#check @SerrePositivity.KST.SConstruction.innerVariableOuterMap_castSucc
#print axioms SerrePositivity.KST.SConstruction.innerVariableOuterMap_castSucc

#check @SerrePositivity.KST.SConstruction.finRotate_castSucc
#print axioms SerrePositivity.KST.SConstruction.finRotate_castSucc

#check @SerrePositivity.KST.SConstruction.innerVariableIndex_obj_permutation
#print axioms SerrePositivity.KST.SConstruction.innerVariableIndex_obj_permutation

#check @SerrePositivity.KST.SConstruction.innerVariableIndex_map_permutation
#print axioms SerrePositivity.KST.SConstruction.innerVariableIndex_map_permutation

#check @SerrePositivity.KST.SConstruction.multiInnerSCoordinateCoreIso
#print axioms SerrePositivity.KST.SConstruction.multiInnerSCoordinateCoreIso

#check @SerrePositivity.KST.SConstruction.multiInnerSCoordinateRealizationIso
#print axioms SerrePositivity.KST.SConstruction.multiInnerSCoordinateRealizationIso

#check @SerrePositivity.KST.SConstruction.multiInnerSCoordinateCoreIso_realization
#print axioms SerrePositivity.KST.SConstruction.multiInnerSCoordinateCoreIso_realization

#check @SerrePositivity.KST.SConstruction.multiInnerSCoordinateAt
#print axioms SerrePositivity.KST.SConstruction.multiInnerSCoordinateAt

#check @SerrePositivity.KST.SConstruction.multiInnerSCoordinateAt_naturality
#print axioms SerrePositivity.KST.SConstruction.multiInnerSCoordinateAt_naturality

#check @SerrePositivity.KST.SConstruction.multiInnerSCoordinateNatIso
#print axioms SerrePositivity.KST.SConstruction.multiInnerSCoordinateNatIso

#check @SerrePositivity.KST.SConstruction.simplicialPathCut_zeroRow_boundary
#print axioms SerrePositivity.KST.SConstruction.simplicialPathCut_zeroRow_boundary

#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalCylinder_zeroRow_boundary
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalCylinder_zeroRow_boundary

#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalCylinder_section
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalCylinder_section

#check @SerrePositivity.KST.SConstruction.rawCofiberCylinderSquare
#print axioms SerrePositivity.KST.SConstruction.rawCofiberCylinderSquare

#check @SerrePositivity.KST.SConstruction.rawCofiberCylinderDesc
#print axioms SerrePositivity.KST.SConstruction.rawCofiberCylinderDesc

#check @SerrePositivity.KST.SConstruction.rawCofiberCylinderDesc_quotient
#print axioms SerrePositivity.KST.SConstruction.rawCofiberCylinderDesc_quotient

#check @SerrePositivity.KST.SConstruction.rawCofiberCylinderDesc_point
#print axioms SerrePositivity.KST.SConstruction.rawCofiberCylinderDesc_point

#check @SerrePositivity.KST.SConstruction.rawCofiberCylinder_hom_ext
#print axioms SerrePositivity.KST.SConstruction.rawCofiberCylinder_hom_ext

#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalBasedContraction
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalBasedContraction

#check @SerrePositivity.KST.SConstruction.simplicialPathDiagonalCylinder_section_quotient
#print axioms SerrePositivity.KST.SConstruction.simplicialPathDiagonalCylinder_section_quotient

#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalCylinder
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalCylinder

#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalCylinder_quotient
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalCylinder_quotient

#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalCylinder_point
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalCylinder_point

#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalCylinder_zero
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalCylinder_zero

#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalCylinder_one
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalCylinder_one

#check @SerrePositivity.KST.SConstruction.reducedPathDiagonalContraction
#print axioms SerrePositivity.KST.SConstruction.reducedPathDiagonalContraction

#check @SerrePositivity.KST.SConstruction.zeroRowPathToQuotient_degeneracy
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathToQuotient_degeneracy

#check @SerrePositivity.KST.SConstruction.zeroRowPathContraction_degeneracy
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathContraction_degeneracy

#check @SerrePositivity.KST.SConstruction.zeroRowPathToQuotient
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathToQuotient

#check @SerrePositivity.KST.SConstruction.zeroRowPathContraction
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathContraction

#check @SerrePositivity.KST.SConstruction.zeroRowPathContraction_raw
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathContraction_raw

#check @SerrePositivity.KST.SConstruction.zeroRowPathContraction_zero
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathContraction_zero

#check @SerrePositivity.KST.SConstruction.zeroRowPathContraction_one
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathContraction_one

#check @SerrePositivity.KST.SConstruction.zeroRowPathContractionHomotopy
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathContractionHomotopy

#check @SerrePositivity.KST.SConstruction.zeroRowPathContraction_boundary
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathContraction_boundary

#check @SerrePositivity.KST.SConstruction.cylinder_boundary_constant
#print axioms SerrePositivity.KST.SConstruction.cylinder_boundary_constant

#check @SerrePositivity.KST.SConstruction.circleCylinderDesc_constant_parameter
#print axioms SerrePositivity.KST.SConstruction.circleCylinderDesc_constant_parameter

#check @SerrePositivity.KST.SConstruction.loopOfCylinder_constant_parameter
#print axioms SerrePositivity.KST.SConstruction.loopOfCylinder_constant_parameter

#check @SerrePositivity.KST.SConstruction.circleCylinderDesc
#print axioms SerrePositivity.KST.SConstruction.circleCylinderDesc

#check @SerrePositivity.KST.SConstruction.circleCylinderDesc_quotient
#print axioms SerrePositivity.KST.SConstruction.circleCylinderDesc_quotient

#check @SerrePositivity.KST.SConstruction.circleCylinderDesc_point
#print axioms SerrePositivity.KST.SConstruction.circleCylinderDesc_point

#check @SerrePositivity.KST.SConstruction.loopOfCylinder
#print axioms SerrePositivity.KST.SConstruction.loopOfCylinder

#check @SerrePositivity.KST.SConstruction.loopOfCylinder_uncurry
#print axioms SerrePositivity.KST.SConstruction.loopOfCylinder_uncurry

#check @SerrePositivity.KST.SConstruction.loopOfCylinder_raw
#print axioms SerrePositivity.KST.SConstruction.loopOfCylinder_raw

#check @SerrePositivity.KST.SConstruction.zeroRowBoundaryCylinder
#print axioms SerrePositivity.KST.SConstruction.zeroRowBoundaryCylinder

#check @SerrePositivity.KST.SConstruction.zeroRowBoundaryCylinder_zero
#print axioms SerrePositivity.KST.SConstruction.zeroRowBoundaryCylinder_zero

#check @SerrePositivity.KST.SConstruction.zeroRowBoundaryCylinder_one
#print axioms SerrePositivity.KST.SConstruction.zeroRowBoundaryCylinder_one

#check @SerrePositivity.KST.SConstruction.zeroRowLoopComparison
#print axioms SerrePositivity.KST.SConstruction.zeroRowLoopComparison

#check @SerrePositivity.KST.SConstruction.zeroRowBoundaryCylinder_degeneracy
#print axioms SerrePositivity.KST.SConstruction.zeroRowBoundaryCylinder_degeneracy

#check @SerrePositivity.KST.SConstruction.zeroRowLoopComparison_degeneracy
#print axioms SerrePositivity.KST.SConstruction.zeroRowLoopComparison_degeneracy

#check @SerrePositivity.KST.SConstruction.zeroRowLoopComparison_raw
#print axioms SerrePositivity.KST.SConstruction.zeroRowLoopComparison_raw

#check @SerrePositivity.KST.SConstruction.zeroRowLoopComparison_assembly
#print axioms SerrePositivity.KST.SConstruction.zeroRowLoopComparison_assembly

#check @SerrePositivity.KST.SConstruction.zeroRowPointedLoopComparison
#print axioms SerrePositivity.KST.SConstruction.zeroRowPointedLoopComparison

#check @SerrePositivity.KST.SConstruction.zeroRowKanLoopComparison
#print axioms SerrePositivity.KST.SConstruction.zeroRowKanLoopComparison

#check @SerrePositivity.KST.SConstruction.zeroRowKanLoopComparison_unit
#print axioms SerrePositivity.KST.SConstruction.zeroRowKanLoopComparison_unit

#check @SerrePositivity.KST.SConstruction.loop_interval_hom_ext
#print axioms SerrePositivity.KST.SConstruction.loop_interval_hom_ext

#check @SerrePositivity.KST.SConstruction.loopOfCylinder_unique
#print axioms SerrePositivity.KST.SConstruction.loopOfCylinder_unique

#check @SerrePositivity.KST.SConstruction.adjoinTensorMap_first
#print axioms SerrePositivity.KST.SConstruction.adjoinTensorMap_first

#check @SerrePositivity.KST.SConstruction.cofiberSmashProjection_first
#print axioms SerrePositivity.KST.SConstruction.cofiberSmashProjection_first

#check @SerrePositivity.KST.SConstruction.rawCofiberTensorDesc_evaluation
#print axioms SerrePositivity.KST.SConstruction.rawCofiberTensorDesc_evaluation

#check @SerrePositivity.KST.SConstruction.suspensionLoopEquiv_eq_smashCurry
#print axioms SerrePositivity.KST.SConstruction.suspensionLoopEquiv_eq_smashCurry

#check @SerrePositivity.KST.SConstruction.suspensionLoopEquiv_interval
#print axioms SerrePositivity.KST.SConstruction.suspensionLoopEquiv_interval

#check @SerrePositivity.KST.SConstruction.oneDirectionSuspensionAssembly_evaluation
#print axioms SerrePositivity.KST.SConstruction.oneDirectionSuspensionAssembly_evaluation

#check @SerrePositivity.KST.SConstruction.oneDirectionAssemblyAdjoint_interval
#print axioms SerrePositivity.KST.SConstruction.oneDirectionAssemblyAdjoint_interval

#check @SerrePositivity.KST.SConstruction.loop_interval_postcomp
#print axioms SerrePositivity.KST.SConstruction.loop_interval_postcomp

#check @SerrePositivity.KST.SConstruction.kanTargetAssemblyAdjoint_interval
#print axioms SerrePositivity.KST.SConstruction.kanTargetAssemblyAdjoint_interval

#check @SerrePositivity.KST.SConstruction.loop_interval_precomp
#print axioms SerrePositivity.KST.SConstruction.loop_interval_precomp

#check @SerrePositivity.KST.SConstruction.iteratedRealizationToKan_cyclic
#print axioms SerrePositivity.KST.SConstruction.iteratedRealizationToKan_cyclic

#check @SerrePositivity.KST.SConstruction.zeroRowLoopComparison_assemblyAdjoint
#print axioms SerrePositivity.KST.SConstruction.zeroRowLoopComparison_assemblyAdjoint

#check @SerrePositivity.KST.SConstruction.zeroRowLoopComparison_reducedAssemblyAdjoint
#print axioms SerrePositivity.KST.SConstruction.zeroRowLoopComparison_reducedAssemblyAdjoint

#check @SerrePositivity.KST.SConstruction.zeroRowReducedLoopComparison
#print axioms SerrePositivity.KST.SConstruction.zeroRowReducedLoopComparison

#check @SerrePositivity.KST.SConstruction.zeroRowReducedLoopComparison_quotient
#print axioms SerrePositivity.KST.SConstruction.zeroRowReducedLoopComparison_quotient

#check @SerrePositivity.KST.SConstruction.zeroRowLoopComparison_fatBoundary
#print axioms SerrePositivity.KST.SConstruction.zeroRowLoopComparison_fatBoundary

#check @SerrePositivity.KST.SConstruction.terminalPointedInterval
#print axioms SerrePositivity.KST.SConstruction.terminalPointedInterval

#check @SerrePositivity.KST.SConstruction.terminalIntervalStart
#print axioms SerrePositivity.KST.SConstruction.terminalIntervalStart

#check @SerrePositivity.KST.SConstruction.terminalIntervalStart_right
#print axioms SerrePositivity.KST.SConstruction.terminalIntervalStart_right

#check @SerrePositivity.KST.SConstruction.terminalIntervalStart_mono
#print axioms SerrePositivity.KST.SConstruction.terminalIntervalStart_mono

#check @SerrePositivity.KST.SConstruction.terminalIntervalStart_inl
#print axioms SerrePositivity.KST.SConstruction.terminalIntervalStart_inl

#check @SerrePositivity.KST.SConstruction.terminalPathSpace
#print axioms SerrePositivity.KST.SConstruction.terminalPathSpace

#check @SerrePositivity.KST.SConstruction.terminalPathSpace_kanComplex
#print axioms SerrePositivity.KST.SConstruction.terminalPathSpace_kanComplex

#check @SerrePositivity.KST.SConstruction.terminalPathStart
#print axioms SerrePositivity.KST.SConstruction.terminalPathStart

#check @SerrePositivity.KST.SConstruction.terminalPathStart_fibration
#print axioms SerrePositivity.KST.SConstruction.terminalPathStart_fibration

#check @SerrePositivity.KST.SConstruction.terminalPathStart_evaluation
#print axioms SerrePositivity.KST.SConstruction.terminalPathStart_evaluation

#check @SerrePositivity.KST.SConstruction.terminalPathFamily_basepoint
#print axioms SerrePositivity.KST.SConstruction.terminalPathFamily_basepoint

#check @SerrePositivity.KST.SConstruction.terminalPathFamily
#print axioms SerrePositivity.KST.SConstruction.terminalPathFamily

#check @SerrePositivity.KST.SConstruction.terminalPathFamily_ι
#print axioms SerrePositivity.KST.SConstruction.terminalPathFamily_ι

#check @SerrePositivity.KST.SConstruction.terminalPathFamily_start
#print axioms SerrePositivity.KST.SConstruction.terminalPathFamily_start

#check @SerrePositivity.KST.SConstruction.terminalPointedInterval_basepoint_anodyne
#print axioms SerrePositivity.KST.SConstruction.terminalPointedInterval_basepoint_anodyne

#check @SerrePositivity.KST.SConstruction.terminalPathSpace_terminal_rlp
#print axioms SerrePositivity.KST.SConstruction.terminalPathSpace_terminal_rlp

#check @SerrePositivity.KST.SConstruction.terminalPathSpace_isContractibleKan
#print axioms SerrePositivity.KST.SConstruction.terminalPathSpace_isContractibleKan

#check @SerrePositivity.KST.SConstruction.terminalSuffixReparametrization
#print axioms SerrePositivity.KST.SConstruction.terminalSuffixReparametrization

#check @SerrePositivity.KST.SConstruction.terminalSuffixReparametrization_start
#print axioms SerrePositivity.KST.SConstruction.terminalSuffixReparametrization_start

#check @SerrePositivity.KST.SConstruction.terminalSuffixReparametrization_end
#print axioms SerrePositivity.KST.SConstruction.terminalSuffixReparametrization_end

#check @SerrePositivity.KST.SConstruction.terminalSuffixReparametrization_zero
#print axioms SerrePositivity.KST.SConstruction.terminalSuffixReparametrization_zero

#check @SerrePositivity.KST.SConstruction.terminalSuffixReparametrization_one
#print axioms SerrePositivity.KST.SConstruction.terminalSuffixReparametrization_one

#check @SerrePositivity.KST.SConstruction.terminalSuffixFamily_basepoint
#print axioms SerrePositivity.KST.SConstruction.terminalSuffixFamily_basepoint

#check @SerrePositivity.KST.SConstruction.terminalSuffixFamily
#print axioms SerrePositivity.KST.SConstruction.terminalSuffixFamily

#check @SerrePositivity.KST.SConstruction.terminalSuffixFamily_start
#print axioms SerrePositivity.KST.SConstruction.terminalSuffixFamily_start

#check @SerrePositivity.KST.SConstruction.terminalSuffixFamily_zero
#print axioms SerrePositivity.KST.SConstruction.terminalSuffixFamily_zero

#check @SerrePositivity.KST.SConstruction.terminalSuffixFamily_one
#print axioms SerrePositivity.KST.SConstruction.terminalSuffixFamily_one

#check @SerrePositivity.KST.SConstruction.terminalPathHomotopyFiber
#print axioms SerrePositivity.KST.SConstruction.terminalPathHomotopyFiber

#check @SerrePositivity.KST.SConstruction.terminalPathFamilyFiberMap
#print axioms SerrePositivity.KST.SConstruction.terminalPathFamilyFiberMap

#check @SerrePositivity.KST.SConstruction.terminalStrictZeroFiberMap
#print axioms SerrePositivity.KST.SConstruction.terminalStrictZeroFiberMap

#check @SerrePositivity.KST.SConstruction.terminalFiberCylinder
#print axioms SerrePositivity.KST.SConstruction.terminalFiberCylinder

#check @SerrePositivity.KST.SConstruction.terminalFiberCylinder_zero
#print axioms SerrePositivity.KST.SConstruction.terminalFiberCylinder_zero

#check @SerrePositivity.KST.SConstruction.terminalFiberCylinder_one
#print axioms SerrePositivity.KST.SConstruction.terminalFiberCylinder_one

#check @SerrePositivity.KST.SConstruction.terminalFiberHomotopy
#print axioms SerrePositivity.KST.SConstruction.terminalFiberHomotopy

#check @SerrePositivity.KST.SConstruction.zeroRowPathContraction_terminalBoundary
#print axioms SerrePositivity.KST.SConstruction.zeroRowPathContraction_terminalBoundary

#check @SerrePositivity.KST.SConstruction.zeroRowTerminalFiberComparison
#print axioms SerrePositivity.KST.SConstruction.zeroRowTerminalFiberComparison

#check @SerrePositivity.KST.SConstruction.zeroRowTerminalLoopFiberComparison
#print axioms SerrePositivity.KST.SConstruction.zeroRowTerminalLoopFiberComparison

#check @SerrePositivity.KST.SConstruction.zeroRowTerminalFiberHomotopy
#print axioms SerrePositivity.KST.SConstruction.zeroRowTerminalFiberHomotopy

#check @SerrePositivity.KST.SConstruction.zeroRowTerminalLoopFiberComparison_projection
#print axioms SerrePositivity.KST.SConstruction.zeroRowTerminalLoopFiberComparison_projection

#check @SerrePositivity.KST.SConstruction.terminalPathBasepoint_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.terminalPathBasepoint_localized_isIso

#check @SerrePositivity.KST.SConstruction.terminalStrictZeroFiberMap_localized_isIso_of_homotopyPullback
#print axioms SerrePositivity.KST.SConstruction.terminalStrictZeroFiberMap_localized_isIso_of_homotopyPullback

#check @SerrePositivity.KST.SConstruction.zeroRowTerminalFiberComparison_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroRowTerminalFiberComparison_localized_isIso

#check @SerrePositivity.KST.SConstruction.zeroRowTerminalLoopFiberComparison_localized_isIso
#print axioms SerrePositivity.KST.SConstruction.zeroRowTerminalLoopFiberComparison_localized_isIso
