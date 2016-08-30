angular.module('keymaerax.controllers').controller('DashboardCtrl.ShutdownDialog', ['$scope', function($scope) {
  $scope.cancel = function() {
      alert("KeYmaera X is shut down. Please close the window and restart the server to continue using KeYmaera X.")
      $window.close();
  }
}]);

angular.module('keymaerax.controllers').controller('DashboardCtrl.ShutdownDialog', ['$scope', function($scope) {
  $scope.noModalForHelpDialogHack = true
}]);

angular.module('keymaerax.controllers').controller('DashboardCtrl.ExtractDB', ['$scope', '$uibModalInstance', function($scope, $uibModalInstance, path) {
    $scope.extractedDatabaseLocation = path
    $scope.close = function() {
        $uibModalInstance.dismiss('cancel');
    }
}]);

angular.module('keymaerax.controllers').controller('DashboardCtrl', ['$scope', '$uibModal', '$cookies', '$http', function ($scope, $uibModal, $cookies, $http) {
  // Set the view for menu active class
  $scope.$on('routeLoaded', function (event, args) {
    $scope.theview = args.theview;
  });

  $scope.noModalForHelpDialogHack = false;

  $scope.mathematicaIsConfigured = true;
  $http.get("/config/mathematicaStatus")
      .success(function(data) {
          if(data.errorThrown) showCaughtErrorMessage($uibModal, data, "Could not retrieve Mathematica status")
          else
              $scope.mathematicaIsConfigured = data.configured;
      });


  $http.get('/users/' + $cookies.get('userId') + '/dashinfo')
      .success(function(data) {
          if(data.errorThrown) showCaughtErrorMessage($uibModal, data, "Could not retrieve dashboard info for user " + $cookies.get('userId'))
          else {
              $scope.open_proof_count = data.open_proof_count;
               $scope.all_models_count = data.all_models_count;
              $scope.proved_models_count = data.proved_models_count;
          }
      });


  $scope.isLocal = false;
  $http.get('/isLocal')
      .success(function(data) {
          if(data.errorThrown) showCaughtErrorMessage($uibModal, data, "Could not determine if the KeYmaera X server is running locally")
          $scope.isLocal = data.success;
      });

  $scope.shutdown = function() {
      var modalInstance = $uibModal.open({
        templateUrl: 'partials/shutdown_dialog.html',
        controller: 'DashboardCtrl.ShutdownDialog',
        backdrop: 'static',
        size: 'sm'
      });

      $http.get("/shutdown");
  };

  $scope.logoff = function() {
      $http.get("/user/logoff");
      document.location.href = "/index_bootstrap.html";
  }

  $scope.extractdb = function() {
      $http.post('/extractdb')
          .success(function(data) {
              var modalInstance = $uibModal.open({
                  templateUrl: 'partials/extractdb.html',
                  controller: 'DashboardCtrl.ExtractDB',
                  backdrop: "static",
                  size: 'md',
                  resolve: {
                      path: function () { return data.path; },
                  }
              });
          })
  };

  $scope.$emit('routeLoaded', {theview: 'dashboard'});
}]);
