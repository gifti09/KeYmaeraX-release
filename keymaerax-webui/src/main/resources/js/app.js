  var keymaeraProofApp = angular.module('keymaeraProofApp', [
  'ngRoute',
  'ngCookies',
  'ngSanitize',
  'ngAnimate',
  'ngTextcomplete',
  'angularTreeview',
  'angularSpinners',
  'ui.tree',
  'cgBusy',
  'diff-match-patch',
  'ui.bootstrap',
  'ui.bootstrap.tabs',
  'ui.bootstrap.tooltip',
  'ui.bootstrap.popover',
  'ui.bootstrap.collapse',
  'ui.bootstrap.accordion',
  'ui.bootstrap.modal',
  'keymaerax.controllers',
  'keymaerax.errorHandlers',
  'keymaerax.interceptors',
  'keymaerax.services',
  'keymaerax.ui.keyevents',
  'keymaerax.ui.mouseevents',
  'keymaerax.ui.directives',
  'keymaerax.ui.tacticeditor',
  'progressMeter',
  'proofProgressChart',
  'formula',
  'mathjaxformula',
  'mathjaxbind',
  'sequent',
  'sequentproof',
  'xeditable',
  'chart.js'
], function($rootScopeProvider) {
  $rootScopeProvider.digestTtl(1000);
});

keymaeraProofApp.run(function(editableOptions) {
  editableOptions.theme = 'bs3';
});

keymaeraProofApp.run(function($templateCache, $http) {
  // cache templates for popovers, otherwise they're only populated on second show
  $http.get('templates/axiomPopoverTemplate.html', { cache: $templateCache });
  $http.get('templates/sequentRuleTemplate.html', { cache: $templateCache });
  $http.get('templates/formulaDndTooltipTemplate.html', { cache: $templateCache });
  $http.get('templates/tacticError.html', { cache: $templateCache });
});

keymaeraProofApp.config(['$routeProvider',
  function($routeProvider) {
    $routeProvider.
      when('/dashboard', {
        templateUrl: 'partials/dashboard.html',
        controller: 'DashboardCtrl'
      }).
      when('/models', {
        templateUrl: 'partials/model-list.html',
        controller: 'ModelListCtrl'
      }).
      when('/tutorials', {
        templateUrl: 'partials/tutorials.html'
      }).
      when('/usage', {
        templateUrl: 'partials/usage.html'
      }).
      when('/syntax', {
        templateUrl: 'partials/syntax.html'
      }).
      when('/models/:modelId', {
        templateUrl: 'partials/model-detail.html',
        controller: 'ModelDetailCtrl'
      }).
      when('/models/:modelId/proofs', {
        templateUrl: 'partials/modelproof-list.html',
        controller: 'ModelProofsCtrl'
      }).
      when('/models/:modelId/proofs/create', {
        //templateUrl: 'partials/proof-detail.html',
        templateUrl: 'partials/proof-create.html',
        controller: 'ModelProofCreateCtrl'
      }).
      when('/proofs', {
        templateUrl: 'partials/proof-list.html',
        controller: 'ProofListCtrl'
      }).
      when('/proofs/:proofId', {
        //templateUrl: 'partials/proof-detail.html',
        templateUrl: 'partials/proofawesome.html',
        controller: 'ProofCtrl'
      }).
      when('/prooftree/:proofId', {
        templateUrl: 'partials/prooftree-hacms.html',
        controller: 'HACMSTreeCtrl'
      }).
      when('/dev', {
        templateUrl: 'partials/dev.html',
        controller: 'DevCtrl'
      }).
      when('/mathematica', {
        templateUrl: 'partials/mathematica_config.html',
        controller: 'MathematicaConfig'
      }).
      when('/license', {
                templateUrl: 'partials/license_dialog.html',
                controller: 'ServerInfoCtrl'
      }).
      otherwise({
        redirectTo: '/dashboard'
      });
  }]);

// triggers for tooltip and popover
keymaeraProofApp.config(['$uibTooltipProvider', function($tooltipProvider) {
  $tooltipProvider.setTriggers({
    'contextmenu': 'blur'
  });
}]);

// intercept all generic ErrorResponses, intercept all requests to add authentication header
keymaeraProofApp.config(['$httpProvider', function($httpProvider) {
  $httpProvider.interceptors.push('ResponseErrorHandler');
  $httpProvider.interceptors.push('authInjector');
}])
